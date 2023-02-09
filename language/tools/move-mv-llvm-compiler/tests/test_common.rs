use anyhow::Context;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug)]
pub struct HarnessPaths {
    pub move_build: PathBuf,
    pub move_mv_llvm_compiler: PathBuf,
}

pub fn get_harness_paths() -> anyhow::Result<HarnessPaths> {
    // Cargo will tell us the location of move-mv-llvm-compiler.
    let move_mv_llvm_compiler = env!("CARGO_BIN_EXE_move-mv-llvm-compiler");
    let move_mv_llvm_compiler = PathBuf::from(move_mv_llvm_compiler);

    // We have to guess where move-ir-compiler is
    let move_build = move_mv_llvm_compiler
        .with_file_name("move-build")
        .with_extension(std::env::consts::EXE_EXTENSION);

    if !move_build.exists() {
        // todo: can we build move-build automatically?

        let is_release = move_build.to_string_lossy().contains("release");
        let suggestion = if is_release {
            "try running `cargo build -p move-compiler --release` first"
        } else {
            "try running `cargo build -p move-compiler` first"
        };
        anyhow::bail!("move-build not built. {suggestion}");
    }

    Ok(HarnessPaths {
        move_build,
        move_mv_llvm_compiler,
    })
}

#[derive(Debug)]
pub struct TestPlan {
    pub name: String,
    /// The move file to be compiled to LLVM IR
    pub move_file: PathBuf,
    /// The build directory, which contains bytecode for multiple modules and
    /// scripts.
    pub build_dir: PathBuf,
    /// Special commands embedded in the test file as comments
    pub directives: Vec<TestDirective>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum TestDirective {
    Ignore,
}

impl TestPlan {
    pub fn should_ignore(&self) -> bool {
        self.directives.contains(&TestDirective::Ignore)
    }
}

pub fn get_test_plan(test_path: &Path) -> anyhow::Result<TestPlan> {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("cargo_manifest_dir");
    let move_file = Path::new(&manifest_dir).join(test_path);

    let name = test_path.to_string_lossy().to_string();
    let move_file = move_file.to_owned();
    let stem = move_file.file_stem().expect("stem").to_string_lossy();
    let build_dir = move_file.with_file_name(format!("{}-build", stem));
    let directives = load_directives(test_path)?;

    Ok(TestPlan {
        name,
        move_file,
        build_dir,
        directives,
    })
}

fn load_directives(test_path: &Path) -> anyhow::Result<Vec<TestDirective>> {
    let mut directives = Vec::new();
    let source = std::fs::read_to_string(test_path)?;

    for line in source.lines() {
        let line = line.trim();
        let line_is_comment = line.starts_with("//");
        if !line_is_comment {
            continue;
        }
        let line = &line[2..].trim();
        if line.starts_with("ignore") {
            directives.push(TestDirective::Ignore);
        }
    }

    Ok(directives)
}

pub fn run_move_build(harness_paths: &HarnessPaths, test_plan: &TestPlan) -> anyhow::Result<()> {
    clean_build_dir(test_plan)?;

    let mut cmd = Command::new(&harness_paths.move_build);
    cmd.arg(&test_plan.move_file);
    cmd.args(["--flavor", "none"]);
    cmd.args(["--out-dir", &test_plan.build_dir.to_str().expect("utf-8")]);

    let output = cmd.output()?;
    if !output.status.success() {
        anyhow::bail!(
            "move-build failed. stderr:\n\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    Ok(())
}

#[derive(Debug)]
pub struct CompilationUnit {
    pub type_: CompilationUnitType,
    pub bytecode: PathBuf,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum CompilationUnitType {
    Script,
    Module,
}

pub fn find_compilation_units(test_plan: &TestPlan) -> anyhow::Result<Vec<CompilationUnit>> {
    let modules_dir = test_plan.build_dir.join("modules");
    let scripts_dir = test_plan.build_dir.join("scripts");

    let dirs = [
        (modules_dir, CompilationUnitType::Module),
        (scripts_dir, CompilationUnitType::Script),
    ];

    let mut units = vec![];

    for (dir, type_) in dirs {
        if !dir.exists() {
            continue;
        }

        for dirent in fs::read_dir(&dir)? {
            let dirent = dirent?;
            let path = dirent.path();
            if path.extension() != Some(&OsStr::new("mv")) {
                continue;
            }

            let bytecode = path;

            units.push(CompilationUnit { type_, bytecode });
        }
    }

    Ok(units)
}

fn clean_build_dir(test_plan: &TestPlan) -> anyhow::Result<()> {
    let modules_dir = test_plan.build_dir.join("modules");
    let scripts_dir = test_plan.build_dir.join("scripts");

    for dir in [modules_dir, scripts_dir] {
        if !dir.exists() {
            continue;
        }

        for dirent in fs::read_dir(&dir)? {
            let dirent = dirent?;
            let path = dirent.path();
            if path.extension() == Some(&OsStr::new("mv")) {
                fs::remove_file(&path)?;
            }
        }
    }

    Ok(())
}

pub fn compile_all_bytecode(
    harness_paths: &HarnessPaths,
    compilation_units: &[CompilationUnit],
    outtype_flag: &str,
    outfile: &dyn Fn(&CompilationUnit) -> PathBuf,
) -> anyhow::Result<()> {
    for cu in compilation_units {
        let mut cmd = Command::new(&harness_paths.move_mv_llvm_compiler);
        cmd.arg("-b");
        cmd.arg(&cu.bytecode);
        cmd.arg("-o");
        cmd.arg(&outfile(&cu));
        cmd.arg(&outtype_flag);

        if cu.type_ == CompilationUnitType::Script {
            cmd.arg("-s");
        }

        let output = cmd.output().context("run move-mv-llvm-compiler failed")?;
        if !output.status.success() {
            anyhow::bail!(
                "move-mv-llvm-compiler failed. stderr:\n\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }

    Ok(())
}

//! Tests of compilation from MVIR to LLVM IR.
//!
//! - Create a test for every .mvir file in testdata/
//! - Run `move-ir-compiler` to convert MVIR to MV bytecode.
//! - Run `move-mv-llvm-compiler` to convert MV bytecode to LLVM IR.
//! - Compare the actual IR to an existing expected IR.
//!
//! If the `PROMOTE_LLVM_IR` env var is set, the actual IR is promoted to the
//! expected IR.

use std::path::{Path, PathBuf};
use std::process::Command;
use similar::{ChangeTag, TextDiff};
use anyhow::Context;

pub const TEST_DIR: &str = "tests/testdata";

datatest_stable::harness!(run_test, TEST_DIR, r".*\.mvir$");

fn run_test(test_path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    Ok(run_test_inner(test_path)?)
}

fn run_test_inner(test_path: &Path) -> anyhow::Result<()> {
    let harness_paths = get_harness_paths()?;
    let test_plan = get_test_plan(test_path);

    //compile_mvir_to_mvbc(&harness_paths, &test_plan)?;
    compile_mvbc_to_llvmir(&harness_paths, &test_plan)?;
    maybe_promote_actual_llvmir_to_expected(&test_plan)?;
    compare_actual_llvmir_to_expected(&test_plan)?;

    Ok(())
}

#[derive(Debug)]
struct HarnessPaths {
    move_ir_compiler: PathBuf,
    move_mv_llvm_compiler: PathBuf,
}

fn get_harness_paths() -> anyhow::Result<HarnessPaths> {
    // Cargo will tell us the location of move-mv-llvm-compiler.
    let move_mv_llvm_compiler = env!("CARGO_BIN_EXE_move-mv-llvm-compiler");
    let move_mv_llvm_compiler = PathBuf::from(move_mv_llvm_compiler);

    // We have to guess where move-ir-compiler is
    let move_ir_compiler = if !cfg!(windows) {
        move_mv_llvm_compiler.with_file_name("move-ir-compiler")
    } else {
        move_mv_llvm_compiler.with_file_name("move-ir-compiler.exe")
    };

    if !move_ir_compiler.exists() {
        // todo: can we build move-ir-compiler automatically?

        let is_release = move_ir_compiler.to_string_lossy().contains("release");
        let suggestion = if is_release {
            "try running `cargo build -p move-ir-compiler --release` first"
        } else {
            "try running `cargo build -p move-ir-compiler` first"
        };
        anyhow::bail!("move-ir-compiler not built. {suggestion}");
    }

    Ok(HarnessPaths {
        move_ir_compiler,
        move_mv_llvm_compiler,
    })
}

#[derive(Debug)]
struct TestPlan {
    /// The mvir file to be compiled to LLVM IR
    mvir_file: PathBuf,
    /// The move bytecode file, compiled from mvir, compiled to LLVM
    mvbc_file: PathBuf,
    /// The final LLVM IR file
    llir_file: PathBuf,
    /// The existing LLVM IR file to compare to
    llir_file_expected: PathBuf,
}

fn get_test_plan(test_path: &Path) -> TestPlan {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("cargo_manifest_dir");
    let test_dir = Path::new(&manifest_dir).join(test_path);

    let mvir_file = test_dir.to_owned();
    let mvbc_file = mvir_file.with_extension("mv");
    let llir_file = mvir_file.with_extension("actual.ll");
    let llir_file_expected = mvir_file.with_extension("expected.ll");

    TestPlan {
        mvir_file,
        mvbc_file,
        llir_file,
        llir_file_expected,
    }
}

/// Run `move-ir-compiler` to produce Move bytecode, `mvbc_file`.
fn compile_mvir_to_mvbc(harness_paths: &HarnessPaths, test_plan: &TestPlan) -> anyhow::Result<()> {
    let mut cmd = Command::new(harness_paths.move_ir_compiler.to_str().expect("PathBuf"));
    cmd.arg("-m");
    cmd.arg(test_plan.mvir_file.to_str().expect("PathBuf"));

    let output = cmd.output().context("run move-ir-compiler failed")?;
    if !output.status.success() {
        anyhow::bail!("move-ir-compiler failed. stderr:\n\n{}",
                      String::from_utf8_lossy(&output.stderr));
    }

    Ok(())
}

/// Run `move-mv-llvm-compiler` to produce LLVM IR, `llir_file`.
fn compile_mvbc_to_llvmir(harness_paths: &HarnessPaths, test_plan: &TestPlan) -> anyhow::Result<()> {
    let mut cmd = Command::new(harness_paths.move_mv_llvm_compiler.to_str().expect("PathBuf"));
    cmd.arg("-b");
    cmd.arg(test_plan.mvbc_file.to_str().expect("PathBuf"));
    cmd.arg("-o");
    cmd.arg(test_plan.llir_file.to_str().expect("PathBuf"));
    cmd.arg("-S");

    let output = cmd.output().context("run move-mv-llvm-compiler failed")?;
    if !output.status.success() {
        anyhow::bail!("move-mv-llvm-compiler failed. stderr:\n\n{}",
                      String::from_utf8_lossy(&output.stderr));
    }

    Ok(())
}

/// Copy actual LLVM IR, `llir_file`, to expected IR, `llir_file_expected`, if `PROMOTE_LLVM_IR` env var is set.
fn maybe_promote_actual_llvmir_to_expected(test_plan: &TestPlan) -> anyhow::Result<()> {
    if std::env::var("PROMOTE_LLVM_IR").is_ok() {
        std::fs::copy(test_plan.llir_file.as_path(), test_plan.llir_file_expected.as_path())?;
    }

    Ok(())
}

/// Compare `llir_file` to `llir_file_expected`.
///
/// If different, print a diff.
fn compare_actual_llvmir_to_expected(test_plan: &TestPlan) -> anyhow::Result<()> {
    if !test_plan.llir_file_expected.exists() {
        anyhow::bail!("no expected.ll file");
    }

    let mut diff_msg = String::new();
    let file_actual = std::fs::read_to_string(test_plan.llir_file.as_path())?;
    let file_expected = std::fs::read_to_string(test_plan.llir_file_expected.as_path())?;

    let diff = TextDiff::from_lines(&file_expected, &file_actual);
    for change in diff.iter_all_changes() {
        let sign = match change.tag() {
            ChangeTag::Delete => Some("-"),
            ChangeTag::Insert => Some("+"),
            ChangeTag::Equal => None,
        };

        if let Some(sign) = sign {
            diff_msg.push_str(&format!("{}{}", sign, change));
        }
    }

    if !diff_msg.is_empty() {
        anyhow::bail!(format!("llvm IR actual does not equal expected: \n\n{}", diff_msg));
    }

    Ok(())
}

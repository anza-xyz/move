use anyhow::Context;
use extension_trait::extension_trait;
use std::path::{Path, PathBuf};
use std::process::Command;
use solana_rbpf as rbpf;

mod test_common;
use test_common as tc;

pub const TEST_DIR: &str = "tests/rbpf-tests";

datatest_stable::harness!(run_test, TEST_DIR, r".*\.move");

fn run_test(test_path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    Ok(run_test_inner(test_path)?)
}

fn run_test_inner(test_path: &Path) -> anyhow::Result<()> {
    let bpf_tools = get_bpf_tools()?;

    let harness_paths = tc::get_harness_paths()?;
    let test_plan = tc::get_test_plan(test_path)?;

    if test_plan.should_ignore() {
        eprintln!("ignoring {}", test_plan.name);
        return Ok(());
    }

    tc::run_move_build(&harness_paths, &test_plan)?;

    let compilation_units = tc::find_compilation_units(&test_plan)?;

    compile_all_bytecode_to_object_files(&harness_paths, &compilation_units)?;

    let exe = link_object_files(&test_plan, &bpf_tools, &compilation_units)?;

    run_rbpf(&exe)?;

    Ok(())
}

#[extension_trait]
impl CompilationUnitExt for tc::CompilationUnit {
    fn object_file(&self) -> PathBuf {
        self.bytecode.with_extension("o")
    }
}

fn compile_all_bytecode_to_object_files(
    harness_paths: &tc::HarnessPaths,
    compilation_units: &[tc::CompilationUnit],
) -> anyhow::Result<()> {
    tc::compile_all_bytecode(
        harness_paths,
        compilation_units,
        "-O",
        &|cu| cu.object_file()
    )
}

struct BpfTools {
    _root: PathBuf,
    clang: PathBuf,
    rustc: PathBuf,
    lld: PathBuf,
}

fn get_bpf_tools() -> anyhow::Result<BpfTools> {
    let bpf_tools_root = std::env::var("BPF_TOOLS_ROOT")
        .context("env var BPF_TOOLS_ROOT not set")?;
    let bpf_tools_root = PathBuf::from(bpf_tools_root);

    let bpf_tools = BpfTools {
        _root: bpf_tools_root.clone(),
        clang: bpf_tools_root.join("llvm/bin/clang")
            .with_extension(std::env::consts::EXE_EXTENSION),
        rustc: bpf_tools_root.join("rust/bin/rustc")
            .with_extension(std::env::consts::EXE_EXTENSION),
        lld: bpf_tools_root.join("llvm/bin/ld.lld"),
    };

    if !bpf_tools.clang.exists() {
        anyhow::bail!("no clang bin at {}", bpf_tools.clang.display());
    }
    if !bpf_tools.rustc.exists() {
        anyhow::bail!("no rustc bin at {}", bpf_tools.rustc.display());
    }
    if !bpf_tools.lld.exists() {
        anyhow::bail!("no lld bin at {}", bpf_tools.lld.display());
    }

    Ok(bpf_tools)
}

#[allow(unused)]
fn link_object_files_(test_plan: &tc::TestPlan, bpf_tools: &BpfTools, compilation_units: &[tc::CompilationUnit]) -> anyhow::Result<PathBuf> {
    let output_dylib = test_plan.build_dir.join("output.so");
    
    let mut cmd = Command::new(&bpf_tools.clang);
    //cmd.arg("--target=bpfel-unknown-unknown");
    cmd.args(["-target", "bpf"]);
    cmd.arg("-fPIC");
    cmd.arg("-march=bpfel+solana");
    cmd.arg(format!("-fuse-ld={}", bpf_tools.lld.display()));
    cmd.arg("-shared"); // create a shared library
    cmd.arg("-o");
    cmd.arg(&output_dylib);
    cmd.arg("-v");

    for cu in compilation_units {
        cmd.arg(&cu.object_file());
    }

    let output = cmd.output()?;
    if !output.status.success() {
        anyhow::bail!(
            "linking with lld failed. stderr:\n\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    Ok(output_dylib)
}

fn link_object_files(test_plan: &tc::TestPlan, bpf_tools: &BpfTools, compilation_units: &[tc::CompilationUnit]) -> anyhow::Result<PathBuf> {
    let output_dylib = test_plan.build_dir.join("output.so");
    
    let mut cmd = Command::new(&bpf_tools.lld);
    cmd.args(["-z", "notext"]);
    cmd.arg("-shared");
    cmd.arg("--Bdynamic");
    cmd.args(["--entry", "main"]);
    cmd.arg("-o");
    cmd.arg(&output_dylib);

    for cu in compilation_units {
        cmd.arg(&cu.object_file());
    }

    let output = cmd.output()?;
    if !output.status.success() {
        anyhow::bail!(
            "linking with lld failed. stderr:\n\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    Ok(output_dylib)
}

fn run_rbpf(exe: &Path) -> anyhow::Result<()> {
    use rbpf::vm::*;
    use rbpf::memory_region::MemoryRegion;
    use rbpf::elf::Executable;
    use rbpf::ebpf;
    use rbpf::verifier::RequisiteVerifier;
    //use rbpf::elf_parser_glue::{GoblinParser, ElfParser};
    use std::sync::Arc;

    let elf = &std::fs::read(exe)?;
    //let parser = GoblinParser::parse(elf)?;
    let mem = &mut vec![0; 1024];

    let config = Config {
        dynamic_stack_frames: false,
        enable_elf_vaddr: false,
        reject_rodata_stack_overlap: false,
        static_syscalls: false,
        optimize_rodata: false,
        new_elf_parser: true,
        .. Config::default()
    };
    let loader = Arc::new(BuiltInProgram::new_loader(config));
    //let function_registry = FunctionRegistry::default();
    let executable = Executable::<TestContextObject>::from_elf(elf, loader).unwrap();
    let mem_region = MemoryRegion::new_writable(mem, ebpf::MM_INPUT_START);
    let verified_executable = VerifiedExecutable::<RequisiteVerifier, TestContextObject>::from_executable(executable).unwrap();
    let mut context_object = TestContextObject::new(1);
    let mut vm = EbpfVm::new(&verified_executable, &mut context_object, &mut [], vec![mem_region]).unwrap();

    let (_instruction_count, _result) = vm.execute_program(true);

    Ok(())
}

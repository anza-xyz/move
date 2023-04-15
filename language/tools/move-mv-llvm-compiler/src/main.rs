// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

#![allow(unused)]

//#![forbid(unsafe_code)]

use anyhow::Context;
use clap::Parser;
use llvm_sys::{core::LLVMContextCreate, prelude::LLVMModuleRef};
use move_binary_format::{
    binary_views::BinaryIndexedView,
    file_format::{CompiledModule, CompiledScript},
};
use move_bytecode_source_map::{mapping::SourceMapping, utils::source_map_from_file};
use move_command_line_common::files::{
    MOVE_COMPILED_EXTENSION, MOVE_EXTENSION, SOURCE_MAP_EXTENSION,
};
use move_ir_types::location::Spanned;
use move_mv_llvm_compiler::disassembler::Disassembler;
use std::{fs, path::Path};

#[derive(Debug, Parser)]
#[clap(author, version, about)]
struct Args {
    /// Skip printing of private functions.
    #[clap(long = "skip-private")]
    pub skip_private: bool,

    /// Do not print the disassembled bytecodes of each function.
    #[clap(long = "skip-code")]
    pub skip_code: bool,

    /// Do not print locals of each function.
    #[clap(long = "skip-locals")]
    pub skip_locals: bool,

    /// Do not print the basic blocks of each function.
    #[clap(long = "skip-basic-blocks")]
    pub skip_basic_blocks: bool,

    /// Treat input file as a script (default is to treat file as a module)
    #[clap(short = 's', long = "script")]
    pub is_script: bool,

    /// The path to the move bytecode file to compile.
    #[clap(short = 'b', long = "bytecode")]
    pub bytecode_file_path: String,

    /// Bytecode dependencies, sorted.
    #[clap(short = 'd', long = "deps")]
    pub bytecode_dependency_paths: Vec<String>,

    /// Path to output file.
    #[clap(short = 'o', default_value = "-")]
    pub output_file_path: String,

    /// Output llvm bitcode in a human readable text format.
    #[clap(short = 'S')]
    pub llvm_ir: bool,

    /// Output an object file
    #[clap(short = 'O')]
    pub obj: bool,

    /// Write or view GraphViz dot graph files for each CFG.
    /// ("write": gen dot files, "view": gen dot files and invoke xdot viewer)"
    #[clap(long = "gen-dot-cfg", default_value = "")]
    pub gen_dot_cfg: String,

    /// Path to GraphViz output files (defaults to current working directory).
    #[clap(long = "dot-out-dir", default_value = "")]
    pub dot_file_path: String,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let move_extension = MOVE_EXTENSION;
    let mv_bytecode_extension = MOVE_COMPILED_EXTENSION;
    let source_map_extension = SOURCE_MAP_EXTENSION;

    let source_path = Path::new(&args.bytecode_file_path);
    let extension = source_path
        .extension()
        .context("Missing file extension for bytecode file")?;
    if extension != mv_bytecode_extension {
        anyhow::bail!(
            "Bad source file extension {:?}; expected {}",
            extension,
            mv_bytecode_extension
        );
    }

    let bytecode_bytes =
        fs::read(&args.bytecode_file_path).context("Unable to read bytecode file")?;

    let mut dep_bytecode_bytes = vec![];
    for dep in &args.bytecode_dependency_paths {
        let bytes = fs::read(dep).context("Unable to read dependency bytecode file {dep}")?;
        dep_bytecode_bytes.push(bytes);
    }

    let source_path = Path::new(&args.bytecode_file_path).with_extension(move_extension);
    let source = fs::read_to_string(&source_path).ok();
    let source_map = source_map_from_file(
        &Path::new(&args.bytecode_file_path).with_extension(source_map_extension),
    );

    let no_loc = Spanned::unsafe_no_loc(()).loc;
    let module: CompiledModule;
    let script: CompiledScript;
    let bytecode = if args.is_script {
        script = CompiledScript::deserialize(&bytecode_bytes)
            .context("Script blob can't be deserialized")?;
        BinaryIndexedView::Script(&script)
    } else {
        module = CompiledModule::deserialize(&bytecode_bytes)
            .context("Module blob can't be deserialized")?;
        BinaryIndexedView::Module(&module)
    };

    let mut source_mapping = {
        if let Ok(s) = source_map {
            SourceMapping::new(s, bytecode)
        } else {
            SourceMapping::new_from_view(bytecode, no_loc)
                .context("Unable to build dummy source mapping")?
        }
    };

    if let Some(source_code) = source {
        source_mapping.with_source_code((source_path.to_str().unwrap().to_string(), source_code));
    }

    let model_env = {
        let main_move_module = if args.is_script {
            let script = CompiledScript::deserialize(&bytecode_bytes)
                .context("Script blob can't be deserialized")?;
            move_model::script_into_module(script)
        } else {
            CompiledModule::deserialize(&bytecode_bytes)
                .context("Module blob can't be deserialized")?
        };

        let mut dep_move_modules = vec![];

        for bytes in &dep_bytecode_bytes {
            let dep_module = CompiledModule::deserialize(bytes)
                .context("Dependency module blob can't be deserialized")?;
            dep_move_modules.push(dep_module);
        }

        let modules = dep_move_modules
            .into_iter()
            .chain(Some(main_move_module))
            .collect::<Vec<_>>();

        move_model::run_bytecode_model_builder(&modules)?
    };

    // let llvm_context = unsafe { LLVMContextCreate() };

    // let move_module = model_env.get_modules().next().expect("module");
    // let mut disassembler = Disassembler::new(source_mapping, move_module, llvm_context);
    // let module = disassembler.disassemble()
    //    .context("Failed to disassemble bytecode")?;
    // disassembler.llvm_write_to_file(module, args.llvm_ir, &args.output_file_path)?;

    if args.llvm_ir && args.obj {
        anyhow::bail!("can't output both LLVM IR (-S) and object file (-O)");
    }

    let dot_info = match (&*args.gen_dot_cfg) {
        "write" => "w:".to_owned() + &args.dot_file_path,
        "view" => "v:".to_owned() + &args.dot_file_path,
        "" => "".to_owned(),
        _ => {
            eprintln!("unexpected gen-dot-cfg option '{}', ignored.", &args.gen_dot_cfg);
            "".to_owned()
        },
    };

    {
        use move_mv_llvm_compiler::stackless::*;

        let mod_id = model_env
            .get_modules()
            .last()
            .map(|m| m.get_id())
            .expect(".");
        let global_cx = GlobalContext::new(&model_env, Target::Solana);
        let mod_cx = global_cx.create_module_context(mod_id, &dot_info);
        let mut llmod = mod_cx.translate();
        if !args.obj {
            llvm_write_to_file(llmod.as_mut(), args.llvm_ir, &args.output_file_path)?;
            drop(llmod);
        } else {
            write_object_file(llmod, Target::Solana, &args.output_file_path)?;
        }

        // NB: context must outlive llvm module
        // fixme this should be handled with lifetimes
        drop(global_cx);
    };

    Ok(())
}

pub fn llvm_write_to_file(
    module: LLVMModuleRef,
    llvm_ir: bool,
    output_file_name: &String,
) -> anyhow::Result<()> {
    use llvm_sys::{
        bit_writer::LLVMWriteBitcodeToFD,
        core::{LLVMDisposeMessage, LLVMPrintModuleToFile, LLVMPrintModuleToString},
    };
    use move_mv_llvm_compiler::support::to_c_str;
    use std::{ffi::CStr, fs::File, os::unix::io::AsRawFd, ptr};

    unsafe {
        if llvm_ir {
            if output_file_name != "-" {
                let mut err_string = ptr::null_mut();
                let res = LLVMPrintModuleToFile(
                    module,
                    to_c_str(&output_file_name).as_ptr(),
                    &mut err_string,
                );

                if res != 0 {
                    assert!(!err_string.is_null());
                    let msg = CStr::from_ptr(err_string).to_string_lossy();
                    LLVMDisposeMessage(err_string);
                    anyhow::bail!("{}", msg);
                }
            } else {
                let buf = LLVMPrintModuleToString(module);
                assert!(!buf.is_null());
                let cstr = CStr::from_ptr(buf);
                print!("{}", cstr.to_string_lossy());
                LLVMDisposeMessage(buf);
            }
        } else {
            if output_file_name == "-" {
                anyhow::bail!("Not writing bitcode to stdout");
            }
            let bc_file = File::create(&output_file_name)?;
            let res = LLVMWriteBitcodeToFD(module, bc_file.as_raw_fd(), false as i32, true as i32);

            if res != 0 {
                anyhow::bail!("Failed to write bitcode to file");
            }
        }
    }

    Ok(())
}

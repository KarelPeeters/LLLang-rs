#![allow(dead_code)]
#![deny(unused_must_use)]

use std::fs::{File, read_to_string, read_dir};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::Clap;
use derive_more::From;

use crate::front::parser::ParseError;
use std::ffi::{OsStr, OsString};
use crate::front::FileId;
use indexmap::map::IndexMap;

mod front;
mod back;
mod mid;
mod util;

#[derive(Debug, From)]
enum CompileError {
    IO(std::io::Error),
    InvalidFileName(OsString),
    Parse(ParseError),
    Lower,
    Assemble,
    Link,
}

type Result<T> = std::result::Result<T, CompileError>;

/// Parse the main file and all of the lib files into a single program
fn parse_all(ll_path: &Path) -> Result<front::ast::Program> {
    let mut modules = IndexMap::new();

    //parse main file
    let main_src = read_to_string(ll_path)?;
    let main_module = front::parser::parse_module(FileId { id: 0 }, &main_src)?;
    modules.insert("".to_owned(), main_module);

    //parse lib files
    let mut next_id = 1;
    //TODO this is brittle, ship the lib files with the exe instead
    for entry in read_dir("lib")? {
        let path = entry?.path();

        if path.extension() == Some(OsStr::new("ll")) {
            let module_name = path.file_stem()
                .and_then(|s| s.to_str())
                .ok_or_else(|| CompileError::InvalidFileName(path.as_os_str().to_owned()))?;

            let id = FileId { id: next_id };
            next_id += 1;

            let module_src = read_to_string(&path);
            let module = front::parser::parse_module(id, &module_src?)?;
            modules.insert(module_name.to_owned(), module);
        }
    }

    Ok(front::ast::Program { modules })
}

fn compile_ll_to_asm(ll_path: &Path) -> Result<PathBuf> {
    println!("----Parser-----");
    let ast = parse_all(ll_path)?;
    let ast_file = ll_path.with_extension("ast");
    File::create(&ast_file)?
        .write_fmt(format_args!("{:#?}", ast))?;

    println!("----Lower------");
    let ir_program = front::lower::lower(&ast)
        .expect("failed to lower"); //TODO ? instead of panic here
    let ir_file = ll_path.with_extension("ir");
    File::create(&ir_file)?
        .write_fmt(format_args!("{}", ir_program))?;

    println!("----Backend----");
    let asm = back::x86_asm::lower(&ir_program);
    let asm_file = ll_path.with_extension("asm");
    File::create(&asm_file)?
        .write_all(asm.as_bytes())?;

    Ok(asm_file)
}

fn compile_asm_to_exe(asm_path: &Path) -> Result<PathBuf> {
    println!("----Assemble---");
    let result = Command::new("nasm")
        .current_dir(asm_path.parent().unwrap())
        .arg("-gcv8")
        .arg("-O0")
        .arg("-fwin32")
        .arg(asm_path.file_name().unwrap())
        .status()?;

    if !result.success() {
        return Err(CompileError::Assemble)
    }

    let result = Command::new("link")
        .current_dir(asm_path.parent().unwrap())
        .arg("/nologo")
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg("/entry:main")
        .arg(asm_path.with_extension("obj").file_name().unwrap())
        .arg("C:\\Program Files (x86)\\Windows Kits\\10\\Lib\\10.0.17763.0\\um\\x86\\kernel32.lib")
        .status()?;

    if !result.success() {
        return Err(CompileError::Link)
    }

    Ok(asm_path.with_extension("exe"))
}

fn run_exe(exe_path: &Path) -> std::io::Result<()> {
    println!("----Running----");
    let result = Command::new(exe_path).status()?;

    println!("{}", result);
    Ok(())
}

#[derive(Clap, Debug)]
struct Opts {
    #[clap(subcommand)]
    command: SubCommand
}

#[derive(Clap, Debug)]
enum SubCommand {
    Run {
        file: String,
    },
    Build {
        file: String,
    },
}

#[derive(Debug)]
enum Level {
    LL,
    ASM,
}

fn main() -> Result<()> {
    //better panic backtraces
    color_backtrace::install();

    let opts: Opts = Opts::parse();

    let (file, do_run) = match opts.command {
        SubCommand::Run { file } => (file, true),
        SubCommand::Build { file } => (file, false),
    };

    let path = Path::new(&file).to_path_buf();

    let level = match path.extension().and_then(|os| os.to_str()) {
        Some("ll") => Level::LL,
        Some("asm") => Level::ASM,
        _ => {
            eprintln!("Expected either .ll or .asm file as input");
            return Ok(())
        }
    };

    let asm_path = match level {
        Level::LL => compile_ll_to_asm(&path)?,
        Level::ASM => path,
    };

    let exe_path = compile_asm_to_exe(&asm_path)?;

    if do_run {
        run_exe(&exe_path)?;
    }

    Ok(())
}
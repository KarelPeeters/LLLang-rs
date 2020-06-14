#![allow(dead_code)]

use std::fs::{File, read_to_string};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::Clap;
use derive_more::From;

use crate::front::parser::ParseError;

mod front;
mod back;
mod mid;
mod util;

#[derive(Debug, From)]
enum CompileError {
    IO(std::io::Error),
    Parse(ParseError),
    Lower,
    Assemble,
    Link,
}

type Result<T> = std::result::Result<T, CompileError>;

fn compile_ll_to_asm(ll_path: &Path) -> Result<PathBuf> {
    let source = read_to_string(ll_path)?;

    println!("----Parser-----");
    let ast = front::parser::parse(&source)
        .expect("failed to parse, unexpected");
    let ast_file = ll_path.with_extension("ast");
    File::create(&ast_file)?
        .write_fmt(format_args!("{:#?}", ast))?;

    println!("----Lower------");
    let ir_program = front::lower::lower(&ast)
        .expect("failed to lower");
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

    //TODO investigate extra build folder with exe files?
    //TODO change nasm and link to run with cwd=build for extra files

    let result = Command::new("link")
        .current_dir(asm_path.parent().unwrap())
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
    println!("{:?}", exe_path);
    println!("----Running----");
    let result = Command::new(exe_path).status()?;

    println!("Exit code: {}", result);
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
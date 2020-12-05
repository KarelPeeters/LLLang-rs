#![allow(dead_code)]
#![deny(unused_must_use)]

use std::ffi::{OsStr, OsString};
use std::fs::{File, read_dir, read_to_string};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::Clap;
use derive_more::From;
use indexmap::map::IndexMap;

use crate::front::FileId;
use crate::front::parser::ParseError;

#[macro_use]
mod util;
mod front;
mod back;
mod mid;

#[derive(Debug, From)]
enum CompileError {
    IO(std::io::Error),
    InvalidFileName(OsString),
    DuplicateModuleName(String),
    Parse(ParseError),
    Lower,
    Assemble,
    Link,
}

type Result<T> = std::result::Result<T, CompileError>;

#[derive(Default)]
struct ModuleCollector {
    modules: IndexMap<String, front::ast::Module>,
    next_file_id: usize,
}

impl ModuleCollector {
    fn add_module_file(&mut self, path: &Path, root: bool) -> Result<()> {
        if root {
            assert!(!self.modules.contains_key(""), "root can only be added once")
        }

        let id = self.next_file_id;
        self.next_file_id += 1;

        let name = if root {
            ""
        } else {
            path.file_stem()
                .and_then(|s| s.to_str())
                .ok_or_else(|| CompileError::InvalidFileName(path.as_os_str().to_owned()))?
        };

        let src = read_to_string(path)?;
        let module = front::parser::parse_module(FileId { id }, &src)?;

        if self.modules.insert(name.to_owned(), module).is_some() {
            Err(CompileError::DuplicateModuleName(name.to_owned()))
        } else {
            Ok(())
        }
    }
}

/// Parse the main file and all of the lib files into a single program
fn parse_all(ll_path: &Path) -> Result<front::ast::Program> {
    let mut collector = ModuleCollector::default();

    //main file
    collector.add_module_file(ll_path, true)?;

    //lib files
    //TODO this is brittle, ship the lib files with the exe instead
    for entry in read_dir("lib")? {
        let path = entry?.path();

        if path.extension() == Some(OsStr::new("ll")) {
            collector.add_module_file(&path, false)?;
        }
    }

    //files in the same folder as the main file
    if let Some(parent_path) = ll_path.parent() {
        for sibling in parent_path.read_dir()? {
            let sibling_path = sibling?.path();
            if sibling_path == ll_path { continue; }

            if sibling_path.extension() == Some(OsStr::new("ll")) {
                collector.add_module_file(&sibling_path, false)?;
            }
        }
    }

    Ok(front::ast::Program { modules: collector.modules })
}

fn run_optimizations(prog: &mut mid::ir::Program) {
    loop {
        let mut changed = false;

        changed |= mid::opt::gc::gc(prog);
        changed |= mid::opt::slot_to_phi::slot_to_phi(prog);
        changed |= mid::opt::gc::gc(prog);
        changed |= mid::opt::sccp::sccp(prog);
        changed |= mid::opt::flow_simplify::flow_simplify(prog);

        if !changed { break; }
    }
}

fn compile_ll_to_asm(ll_path: &Path) -> Result<PathBuf> {
    println!("----Parser-----");
    let ast_program = parse_all(ll_path)?;
    let ast_file = ll_path.with_extension("ast");
    File::create(&ast_file)?
        .write_fmt(format_args!("{:#?}", ast_program))?;

    println!("----Lower------");
    let mut ir_program = front::lower::lower(&ast_program)
        .expect("failed to lower"); //TODO ? instead of panic here
    let ir_file = ll_path.with_extension("ir");
    File::create(&ir_file)?
        .write_fmt(format_args!("{}", ir_program))?;

    println!("----Optimize---");
    run_optimizations(&mut ir_program);
    let ir_opt_file = ll_path.with_extension("ir_opt");
    File::create(&ir_opt_file)?
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
        return Err(CompileError::Assemble);
    }

    let result = Command::new("C:\\Program Files (x86)\\Microsoft Visual Studio\\2019\\BuildTools\\VC\\Tools\\MSVC\\14.27.29110\\bin\\Hostx64\\x86\\link.exe")
        .current_dir(asm_path.parent().unwrap())
        .arg("/nologo")
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg("/entry:main")
        .arg(asm_path.with_extension("obj").file_name().unwrap())
        .arg("C:\\Program Files (x86)\\Windows Kits\\10\\Lib\\10.0.18362.0\\um\\x86\\kernel32.lib")
        .status()?;

    if !result.success() {
        return Err(CompileError::Link);
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
            return Ok(());
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
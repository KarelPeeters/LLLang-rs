#![deny(unused_must_use)]

use std::ffi::{OsStr, OsString};
use std::fs::{File, read_to_string};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::Clap;
use derive_more::From;
use itertools::Itertools;
use walkdir::{DirEntry, WalkDir};

use lllang::{back, front, mid};
use lllang::front::ast;
use lllang::front::parser::ParseError;
use lllang::front::pos::FileId;

#[derive(Debug, From)]
enum CompileError {
    IO(std::io::Error, String),
    Walk(walkdir::Error),
    InvalidFileName(OsString),
    DuplicateModule(String),
    Parse(ParseError),
    Assemble,
    Link,
}

type CompileResult<T> = Result<T, CompileError>;

trait IoError {
    type T;
    fn with_context<S: Into<String>>(self, f: impl FnOnce() -> S) -> CompileResult<Self::T>;
}

impl<T> IoError for Result<T, std::io::Error> {
    type T = T;
    fn with_context<S: Into<String>>(self, f: impl FnOnce() -> S) -> CompileResult<T> {
        self.map_err(|e| CompileError::IO(e, f().into()))
    }
}

fn parse_and_add_module_if_ll(
    prog: &mut front::Program<Option<ast::ModuleContent>>,
    file_count: &mut usize,
    entry: DirEntry,
    skip_path_components: usize,
) -> CompileResult<()> {
    let path = entry.path();

    //check that this is a .ll file
    if !entry.metadata()?.is_file() || path.extension() != Some(OsStr::new("ll")) {
        return Ok(());
    }

    //convert the file path to a proper module path
    let clean_path = path.with_extension("");
    let path_vec: Vec<_> = clean_path.components().skip(skip_path_components)
        .map(|c| {
            let s = c.as_os_str();
            s.to_str()
                .map(|s| s.to_string())
                .ok_or_else(|| CompileError::InvalidFileName(s.to_os_string()))
        })
        .try_collect()?;

    //find the module
    let module_name = path_vec.last().unwrap().clone();
    let module = prog.find_or_create_module(path_vec);

    //if this module already has content that means it's declared twice
    if module.content.is_some() {
        return Err(CompileError::DuplicateModule(module_name));
    }

    //increment the file id
    let id = FileId(*file_count);
    *file_count += 1;

    println!("{:?}: {:?}", id, path);

    //load and parse the source code
    let src = read_to_string(path).with_context(|| format!("Reading module {:?}", path))?;
    let module_ast = front::parser::parse_module(id, &src)?;

    module.content = Some(module_ast);
    Ok(())
}

/// Parse the main file and all of the lib files into a single program
fn parse_all(ll_path: &Path, include_std: bool) -> CompileResult<front::Program<Option<ast::ModuleContent>>> {
    let mut prog = front::Program::default();
    let mut file_count: usize = 0;

    //add stdlib files
    if include_std {
        //TODO this is brittle, ship the lib files with the exe instead
        for file in WalkDir::new("lib") {
            parse_and_add_module_if_ll(&mut prog, &mut file_count, file?, 1)?;
        }
    }

    //add project files
    let parent = ll_path.parent().expect("input file should be in folder");
    let parent_component_count = parent.components().count();

    for file in WalkDir::new(parent) {
        parse_and_add_module_if_ll(&mut prog, &mut file_count, file?, parent_component_count)?;
    }

    Ok(prog)
}

fn run_optimizations(prog: &mut mid::ir::Program) {
    let opts: &[fn(&mut mid::ir::Program) -> bool] = &[
        mid::opt::slot_to_phi::slot_to_phi,
        mid::opt::sccp::sccp,
        mid::opt::flow_simplify::flow_simplify,
        mid::opt::inline::inline,
    ];

    // TODO remove assertion checks that GC is idempotent
    mid::opt::gc::gc(prog);
    assert!(!mid::opt::gc::gc(prog));

    loop {
        let mut changed = false;

        for opt in opts {
            if opt(prog) {
                mid::opt::gc::gc(prog);
                assert!(!mid::opt::gc::gc(prog));

                changed = true;
            }
        }

        if !changed { break; }
    }
}

fn compile_ll_to_asm(ll_path: &Path, include_std: bool, optimize: bool) -> CompileResult<PathBuf> {
    println!("----Parse------");
    let ast_program = parse_all(ll_path, include_std)?;
    let ast_file = ll_path.with_extension("ast");
    File::create(&ast_file).with_context(|| format!("Creating ast file {:?}", ast_file))?
        .write_fmt(format_args!("{:#?}", ast_program)).with_context(|| "Writing to ast file")?;

    println!("----Collect----");
    let resolved = front::resolve::resolve(&ast_program)
        .expect("failed to collect"); //TODO ? instead of panic here
    let cst_file = ll_path.with_extension("cst");
    File::create(&cst_file).with_context(|| format!("Creating cst file {:?}", cst_file))?
        .write_fmt(format_args!("{:#?}", resolved)).with_context(|| "Writing to cst file")?;

    println!("----Lower------");
    let mut ir_program = front::lower::lower(resolved)
        .expect("failed to lower"); //TODO ? instead of panic here
    let ir_file = ll_path.with_extension("ir");
    File::create(&ir_file).with_context(|| format!("Creating IR file {:?}", ir_file))?
        .write_fmt(format_args!("{}", ir_program)).with_context(|| "Writing to IR file")?;

    println!("----Optimize---");
    let ir_opt_file = ll_path.with_extension("ir_opt");
    if optimize {
        run_optimizations(&mut ir_program);
        File::create(&ir_opt_file).with_context(|| format!("Creating IR opt file {:?}", ir_opt_file))?
            .write_fmt(format_args!("{}", ir_program)).with_context(|| "Writing to IR opt file")?;
    } else {
        //clear file
        File::create(&ir_opt_file).with_context(|| format!("Creating IR opt file {:?}", ir_opt_file))?.write_all(&[]).with_context(|| "Clearing IR opt file")?;
    }

    println!("----Backend----");
    let asm = back::x86_asm::lower(&ir_program);
    let asm_file = ll_path.with_extension("asm");
    File::create(&asm_file).with_context(|| format!("Creating ASM file {:?}", asm_file))?
        .write_all(asm.as_bytes()).with_context(|| "Writing to ASM file")?;

    Ok(asm_file)
}

fn compile_asm_to_exe(asm_path: &Path) -> CompileResult<PathBuf> {
    println!("----Assemble---");
    let result = Command::new("nasm")
        .current_dir(asm_path.parent().unwrap())
        .arg("-O0")
        .arg("-fwin32")
        .arg("-g")
        .arg(asm_path.file_name().unwrap())
        .status().with_context(|| "Running nasm")?;

    if !result.success() {
        return Err(CompileError::Assemble);
    }

    let result = Command::new(r#"C:\Program Files (x86)\Microsoft Visual Studio\2019\Community\VC\Tools\MSVC\14.29.30133\bin\Hostx64\x86\link.exe"#)
        .current_dir(asm_path.parent().unwrap())
        .arg("/nologo")
        .arg("/debug")
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg("/entry:main")
        .arg(asm_path.with_extension("obj").file_name().unwrap())
        .arg(r#"C:\Program Files (x86)\Windows Kits\10\Lib\10.0.19041.0\um\x86\kernel32.lib"#)
        .status().with_context(|| "Running link.exe")?;

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
    #[clap(long)]
    no_std: bool,

    #[clap(long)]
    no_opt: bool,

    #[clap(subcommand)]
    command: SubCommand,
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

fn main() -> CompileResult<()> {
    let opts: Opts = Opts::parse();

    let (file, do_run) = match opts.command {
        SubCommand::Run { file } => (file, true),
        SubCommand::Build { file } => (file, false),
    };

    let path = Path::new(&file).to_path_buf();

    //TODO change main so you have to pass the project folder instead of the source name
    //  hmm, that's not entirely great, maybe add a mode for single-file projects too?
    let level = match path.extension().and_then(|os| os.to_str()) {
        Some("ll") => Level::LL,
        Some("asm") => Level::ASM,
        _ => {
            eprintln!("Expected either .ll or .asm file as input");
            return Ok(());
        }
    };

    let asm_path = match level {
        Level::LL => compile_ll_to_asm(&path, !opts.no_std, !opts.no_opt)?,
        Level::ASM => path,
    };

    let exe_path = compile_asm_to_exe(&asm_path)?;

    if do_run {
        run_exe(&exe_path).with_context(|| format!("Running executable {:?}", exe_path))?;
    }

    Ok(())
}
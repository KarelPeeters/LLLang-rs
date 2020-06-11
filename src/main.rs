#![allow(dead_code)]

use std::fs::{File, read_to_string};
use std::io::Write;
use std::path::Path;
use std::process::Command;

mod front;
mod back;
mod mid;
mod util;

pub fn write_output<P: AsRef<Path>>(name: P, string: &str) -> std::io::Result<()> {
    let path = Path::new("ignored/build/").join(name);

    let mut file = File::create(path)?;
    file.write_all(string.as_bytes())?;
    Ok(())
}

fn assemble_and_link() -> std::io::Result<bool> {
    println!("Assembling...");
    let result = Command::new("nasm")
        .current_dir("ignored/build")
        .arg("-fwin32")
        .arg("main.asm")
        .status()?;

    if !result.success() { return Ok(false) }

    println!("Linking...");
    let result = Command::new("link")
        .current_dir("ignored/build")
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg("/entry:main")
        .arg("main.obj")
        .arg("C:\\Program Files (x86)\\Windows Kits\\10\\Lib\\10.0.17763.0\\um\\x86\\kernel32.lib")
        .status()?;

    Ok(result.success())
}

fn run_exe() -> std::io::Result<()> {
    let result = Command::new("ignored/build/main.exe")
        .current_dir("ignored/build")
        .status()?;

    println!("Exit code: {}", result);
    Ok(())
}

fn compile() -> std::io::Result<()> {
    let source = read_to_string("ignored/src/main.ll")?;

    println!("----Parser-----");
    let ast_func = front::parser::parse(&source)
        .expect("failed to parse, unexpected");
    write_output("main.ast", &format!("{:#?}", ast_func))?;

    println!("----Lower------");
    let ir_program = front::lower::lower(&ast_func).expect("failed to lower");
    write_output("main.ir", &format!("{}", ir_program))?;

    // println!("----Emulator----");
    // let emulator_result = back::emulator::run(&ir_program);
    // println!("--------Emulator----==\n{:?}\n\n", emulator_result);

    println!("----Backend----");
    let asm = back::x86_asm::lower(&ir_program);
    write_output("main.asm", &asm)?;

    Ok(())
}

fn main() -> std::io::Result<()> {
    std::fs::create_dir_all("ignored/build")?;

    color_backtrace::install();
    compile()?;

    println!("----NASM-------");
    if assemble_and_link()? {
        println!("----Running----");
        run_exe()?;
    }

    Ok(())
}
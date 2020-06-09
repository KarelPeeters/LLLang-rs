#![allow(dead_code)]

use std::fs::{File, read_to_string};
use std::io::Write;
use std::process::Command;

mod front;
mod back;
mod mid;
mod util;

//TODO proper error handling
fn assemble_and_link(asm: &str) -> std::io::Result<bool> {
    std::fs::create_dir_all("ignored/build")?;
    let mut file = File::create("ignored/build/main.asm")?;
    file.write_all(asm.as_bytes())?;
    drop(file);

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

    // println!("========AST===========");
    let ast_func = front::parser::parse(&source).expect("failed to parse");
    // println!("{:#?}\n\n", ast_func);

    println!("========IR============");
    let ir_program = front::lower::lower(&ast_func).expect("failed to resolve");
    println!("{:}\n\n", ir_program);

    println!("========Emulator======");
    let emulator_result = back::emulator::run(&ir_program);
    println!("{:?}\n\n", emulator_result);

    println!("========ASM===========");
    let asm = back::x86_asm::lower(&ir_program);
    println!("{}\n", asm);

    if assemble_and_link(&asm)? {
        run_exe()?;
    }

    Ok(())
}

fn main() -> std::io::Result<()> {
    color_backtrace::install();
    compile()
}
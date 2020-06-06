#![allow(dead_code)]

use std::fs::read_to_string;

mod front;
mod back;
mod mid;
mod util;

fn compile() {
    let source = read_to_string("ignored/main.ll")
        .expect("failed to read source");

    let ast_func = front::parser::parse(&source)
        .expect("failed to parse");
    println!("========AST===========\n{:#?}\n\n", ast_func);

    let ir_program = front::lower::lower(&ast_func)
        .expect("Failed to resolve");
    println!("========IR============\n{:#?}\n\n", ir_program);

    println!("========Emulator======");
    let result = back::emulator::run(&ir_program);
    println!("Result: {:?}", result);
}

fn main() {
    compile()
}
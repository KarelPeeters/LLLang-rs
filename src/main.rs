use std::fs::read_to_string;

pub mod front;
pub mod back;
pub mod mid;

fn compile() {
    let source = read_to_string("ignored/main.ll")
        .expect("failed to read source");

    let ast_func = front::parser::parse(&source)
        .expect("failed to parse");
    println!("=========AST========= \n{:#?}\n\n", ast_func);

    let ir_func = front::resolve::resolve(&ast_func)
        .expect("Failed to resolve");
    println!("=========IR========== \n{:#?}\n\n", ir_func);

    let result = back::emulator::run(&ir_func);
    println!("Result: {:?}", result);
}

fn main() {
    compile()
}
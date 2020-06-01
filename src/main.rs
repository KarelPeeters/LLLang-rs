use std::fs::read_to_string;

pub mod front;
pub mod back;
pub mod mid;

fn main() {
    let source = read_to_string("ignored/main.ll")
        .expect("failed to read source");

    let function = front::parser::parse(&source);
    println!("{:?}", function);
}

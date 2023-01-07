use lllang::mid::ir;
use lllang::mid::util::bit_int::BitInt;
use lllang::mid::util::verify::verify;

use crate::root::util::{get_debug_func, parse_ir_standalone};

#[test]
fn simple_test() {
    let mut prog = parse_ir_standalone(r#"
        fn main() -> u32 { return 0; }
        fn foo(x: u32) -> u32 { return x + 1; }
    "#);

    let foo = get_debug_func(&prog, "foo");
    prog.root_functions.insert("foo".to_string(), foo);

    println!("======================== Before ========================");
    println!("{}", prog);
    verify(&prog).unwrap();

    let foo_cloned = prog.deep_clone_function(foo).unwrap();
    let foo_cloned = prog.define_func(foo_cloned);
    prog.get_func_mut(foo_cloned).debug_name = Some("foo_cloned".to_owned());
    prog.root_functions.insert("foo_cloned".to_string(), foo_cloned);

    println!("======================== After =========================");
    println!("{}", prog);
    verify(&prog).unwrap();
}

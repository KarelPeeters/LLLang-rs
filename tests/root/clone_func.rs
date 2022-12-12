use lllang::mid::ir::Const;

use crate::root::util::{get_debug_func, parse_ir_standalone};

#[test]
fn simple_test() {
    let mut prog = parse_ir_standalone(r#"
        fn foo(x: int) -> int { return x + 1; }
        fn main() -> int { return foo(4); }
    "#);

    let foo = get_debug_func(&prog, "foo");
    println!("======================== Before ========================");
    println!("{}", prog);

    let foo1 = prog.deep_clone_function(foo, None);
    let foo1 = prog.define_func(foo1);
    prog.get_func_mut(foo1).debug_name = Some("foo1".to_owned());

    let ty_int = prog.define_type_int(32);
    let const_2 = Const::new(ty_int, 2);

    let foo2 = prog.deep_clone_function(foo, Some(&[const_2.into()]));
    let foo2 = prog.define_func(foo2);
    prog.get_func_mut(foo2).debug_name = Some("foo2".to_owned());

    println!("======================== After =========================");
    println!("{}", prog);
}

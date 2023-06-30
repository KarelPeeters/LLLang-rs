use crate::root::full::runner::run_cases;

mod runner;

#[test]
fn arith() {
    run_cases(include_str!("arith.ll"))
}

#[test]
fn lang() {
    run_cases(include_str!("lang.ll"))
}

#[test]
fn seq() {
    run_cases(include_str!("seq.ll"))
}

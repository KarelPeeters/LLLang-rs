use crate::root::full::runner::run_cases;

mod runner;

#[test]
fn arith() {
    run_cases(include_str!("arith.ll"))
}

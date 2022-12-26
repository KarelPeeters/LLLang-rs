use rand::rngs::StdRng;
use rand::{Rng, SeedableRng, thread_rng};
use rand::seq::SliceRandom;
use lllang::mid::ir::{BlockInfo, FunctionInfo, FunctionType, Program, Target, Terminator, Value};
use lllang::mid::util::verify::verify;

#[test]
fn fuzz_main() {
    let mut prog = Program::default();
    let rng = &mut StdRng::seed_from_u64(0);

    let types = vec![prog.ty_void(), prog.ty_bool(), prog.ty_ptr(), prog.ty_isize()];

    let func_ty_info = FunctionType {
        params: (0..rng.gen_range(0..4)).map(|_| *types.choose(rng).unwrap()).collect(),
        ret: *types.choose(rng).unwrap(),
    };

    let block_info = BlockInfo {
        phis: vec![],
        instructions: vec![],
        terminator: Terminator::Return { value: Value::Void },
    };
    let block = prog.define_block(block_info);

    let func_info = FunctionInfo::new(func_ty_info, &mut prog);
    let func = prog.define_func(func_info);

    println!("{}", prog);
    verify(&prog).unwrap();
}

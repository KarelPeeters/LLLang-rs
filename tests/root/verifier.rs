use lllang::mid::ir::{BlockInfo, FunctionInfo, FunctionType, InstructionInfo, PhiInfo, Program, StackSlotInfo, Target, Terminator, Value};
use lllang::mid::util::verify::verify;

#[test]
fn slot_used_in_phi() {
    let mut prog = Program::default();

    let bits = 32;
    let ty = prog.define_type_int(bits);

    let slot = prog.define_slot(StackSlotInfo { inner_ty: ty, debug_name: None });
    let phi = prog.define_phi(PhiInfo { ty: prog.ty_ptr() });

    let block_info = BlockInfo {
        phis: vec![phi],
        instructions: vec![],
        terminator: Terminator::Return { value: Value::void() },
    };
    let block = prog.define_block(block_info);

    let func_ty = FunctionType { params: vec![], ret: prog.ty_void() };
    let mut func_info = FunctionInfo::new(func_ty, &mut prog);

    func_info.slots.push(slot);
    func_info.entry = Target {
        block,
        phi_values: vec![slot.into()],
    };

    let func = prog.define_func(func_info);

    let call = prog.define_instr(InstructionInfo::Call {
        target: func.into(),
        args: vec![],
    });
    let main_block = prog.get_block_mut(prog.get_func(prog.main).entry.block);
    main_block.instructions.push(call);
    main_block.terminator = Terminator::Return { value: Value::void() };

    println!("{}", prog);

    // check that this passes verification
    verify(&prog).unwrap();
}
use lllang::mid::ir::{BlockInfo, CallingConvention, FunctionInfo, FunctionType, InstructionInfo, ParameterInfo, Program, StackSlotInfo, Target, Terminator, Value};
use lllang::mid::util::verify::verify;

#[test]
fn slot_used_in_param() {
    let mut prog = Program::new(64);

    let bits = 32;
    let ty = prog.define_type_int(bits);

    let slot = prog.define_slot(StackSlotInfo { inner_ty: ty, debug_name: None });
    let param = prog.define_param(ParameterInfo { ty: prog.ty_ptr() });

    let block_info = BlockInfo {
        params: vec![param],
        instructions: vec![],
        terminator: Terminator::Return { value: Value::void() },
        debug_name: None,
    };
    let block = prog.define_block(block_info);

    let entry_info = BlockInfo {
        params: vec![],
        instructions: vec![],
        terminator: Terminator::Jump { target: Target { block, args: vec![slot.into()] } },
        debug_name: None,
    };
    let entry = prog.define_block(entry_info);

    let conv = CallingConvention::Custom;
    let func_ty = FunctionType { params: vec![], ret: prog.ty_void(), conv };
    let mut func_info = FunctionInfo::new(func_ty, &mut prog);

    func_info.slots.push(slot);
    func_info.entry = entry;

    let func = prog.define_func(func_info);

    let call = prog.define_instr(InstructionInfo::Call {
        target: func.into(),
        args: vec![],
        conv,
    });

    let main_ty = FunctionType { params: vec![], ret: prog.ty_void(), conv };
    let main_info = FunctionInfo::new(main_ty, &mut prog);

    let main_block = prog.get_block_mut(main_info.entry);
    main_block.instructions.push(call);
    main_block.terminator = Terminator::Return { value: Value::void() };

    let main = prog.define_func(main_info);
    prog.root_functions.insert("main".to_string(), main);

    println!("{}", prog);

    // check that this passes verification
    verify(&prog).unwrap();
}
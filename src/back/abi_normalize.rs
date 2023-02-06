use std::collections::HashMap;

use fixedbitset::FixedBitSet;
use itertools::Itertools;

use crate::back::layout::Layout;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{CallingConvention, Function, FunctionType, InstructionInfo, ParameterInfo, Program, StackSlotInfo, Terminator, Type, Value};

pub fn abi_normalize(prog: &mut Program) {
    let use_info = UseInfo::new(prog);

    for func in use_info.funcs() {
        let func_info = &prog.nodes.funcs[func];
        let changes = changes_for(prog, &func_info.func_ty);

        fixup_signature(prog, &use_info, func, &changes);
        fixup_instructions(prog, &use_info, func, &changes);
    }
}

fn fixup_signature(prog: &mut Program, use_info: &UseInfo, func: Function, changes: &AbiChanges) {
    let ty_ptr = prog.ty_ptr();
    let ty_void = prog.ty_void();

    let entry = prog.get_func(func).entry;

    // replace params with pointers and loads
    let mut replacements = vec![];

    for (index, param) in prog.nodes.blocks[entry].params.iter_mut().enumerate() {
        let old_param = *param;
        let old_ty = prog.nodes.params[old_param].ty;

        if changes.replace_param_with_ptr[index] {
            let new_param = prog.nodes.params.push(ParameterInfo { ty: ty_ptr });
            *param = new_param;

            let load = InstructionInfo::Load { addr: new_param.into(), ty: old_ty };
            let load = prog.nodes.instrs.push(load);
            replacements.push((old_param, load));
        } else {
            // we don't need to change anything
        }
    }

    for &(old_param, load) in &replacements {
        use_info.replace_value_usages(prog, old_param.into(), load.into());
    }
    drop(
        prog.nodes.blocks[entry].instructions
            .splice(0..0, replacements.iter().map(|&(_, load)| load))
    );

    // replace return with pointer
    let func_info = &prog.nodes.funcs[func];

    let new_ret_ty = match changes.replace_ret {
        ChangeReturn::Keep => func_info.func_ty.ret,
        ChangeReturn::Ptr { return_ptr_again } => {
            let new_param = prog.define_param(ParameterInfo { ty: ty_ptr });
            prog.get_block_mut(entry).params.insert(0, new_param);

            if return_ptr_again {
                ty_ptr
            } else {
                ty_void
            }
        }
    };

    // actually update signature
    {
        let new_params = prog.get_block(entry).params.iter()
            .map(|&p| prog.get_param(p).ty)
            .collect_vec();
        let conv = prog.nodes.funcs[func].func_ty.conv;
        let new_func_ty_func = FunctionType { params: new_params, ret: new_ret_ty, conv };
        let new_func_ty = prog.define_type_func(new_func_ty_func.clone());

        let func_info = prog.get_func_mut(func);
        func_info.func_ty = new_func_ty_func;
        func_info.ty = new_func_ty;
    }
}

fn fixup_instructions(prog: &mut Program, use_info: &UseInfo, func: Function, parent_changes: &AbiChanges) {
    // additional replacement map to ensure replaced return values are properly replaced when used as arguments
    let mut replacements: HashMap<Value, Value> = Default::default();

    for &block in use_info.func_blocks(func) {
        let mut index = 0;
        let mut instr_count = prog.get_block(block).instructions.len();

        // fix calls
        while index < instr_count {
            let mut step_size = 1;
            let instr = prog.get_block(block).instructions[index];

            if let &InstructionInfo::Call { target, ref args, conv: _ } = prog.get_instr(instr) {
                let target_ty = prog.type_of_value(target);
                let target_ty_func = prog.get_type(target_ty).unwrap_func().unwrap();
                let changes = changes_for(prog, target_ty_func);
                let args = args.clone();

                // TODO fix calls
                let mut new_args: Vec<Value> = vec![];
                let mut new_slots = vec![];
                match changes.replace_ret {
                    ChangeReturn::Keep => {}
                    ChangeReturn::Ptr { .. } => {
                        let ret_ty = target_ty_func.ret;
                        let slot = prog.define_slot(StackSlotInfo { inner_ty: ret_ty, debug_name: None });
                        new_slots.push(slot);
                        new_args.push(slot.into());

                        // insert load behind call
                        let load = prog.define_instr(InstructionInfo::Load {
                            addr: slot.into(),
                            ty: ret_ty,
                        });
                        prog.get_block_mut(block).instructions.insert(index + 1, load);
                        step_size += 1;
                        instr_count += 1;

                        // register replacement
                        use_info.replace_value_usages(prog, instr.into(), load.into());
                        replacements.insert(instr.into(), load.into());
                    }
                }

                for (arg_index, &old_arg) in args.iter().enumerate() {
                    let arg = replacements.get(&old_arg).copied().unwrap_or(old_arg);

                    if changes.replace_param_with_ptr[arg_index] {
                        let arg_ty = prog.type_of_value(arg);
                        let slot = prog.define_slot(StackSlotInfo { inner_ty: arg_ty, debug_name: None });
                        new_slots.push(slot);
                        new_args.push(slot.into());

                        // insert store before call
                        let store = prog.define_instr(InstructionInfo::Store {
                            addr: slot.into(),
                            ty: arg_ty,
                            value: arg,
                        });
                        prog.get_block_mut(block).instructions.insert(index, store);
                        index += 1;
                        instr_count += 1;
                    }
                }

                let func = prog.get_func_mut(func);
                func.slots.extend_from_slice(&new_slots);

                let old_args = unwrap_match!(
                    prog.get_instr_mut(instr),
                    InstructionInfo::Call { args, .. } => args
                );
                *old_args = new_args;
            }

            assert!(instr_count == prog.get_block(block).instructions.len());
            assert!(index  + step_size <= instr_count);
            index += step_size;
        }

        // fix return
        match parent_changes.replace_ret {
            ChangeReturn::Keep => {}
            ChangeReturn::Ptr { return_ptr_again } => {
                if let Terminator::Return { value } = prog.get_block(block).terminator {
                    let entry = prog.get_func(func).entry;
                    let ptr = prog.get_block(entry).params[0];

                    let store = InstructionInfo::Store {
                        addr: ptr.into(),
                        ty: prog.type_of_value(value),
                        value,
                    };
                    let store = prog.define_instr(store);
                    let block_mut = prog.get_block_mut(block);
                    block_mut.instructions.push(store);

                    let ret_value = if return_ptr_again {
                        ptr.into()
                    } else {
                        Value::void()
                    };
                    block_mut.terminator = Terminator::Return { value: ret_value };
                }
            }
        }
    }
}

#[derive(Debug)]
struct AbiChanges {
    replace_param_with_ptr: FixedBitSet,
    replace_ret: ChangeReturn,
}

#[derive(Debug, Copy, Clone)]
enum ChangeReturn {
    Keep,
    Ptr { return_ptr_again: bool },
}

fn changes_for(prog: &Program, ty: &FunctionType) -> AbiChanges {
    let &FunctionType { ref params, ret, conv } = ty;

    match conv {
        CallingConvention::Win64 => {}
        CallingConvention::Custom => {}
    }

    let mut replace_param_with_ptr = FixedBitSet::with_capacity(ty.params.len());
    for (param_index, &param) in params.iter().enumerate() {
        replace_param_with_ptr.set(param_index, win64_replace_with_ptr(prog, param));
    }

    let replace_ret_with_ptr = win64_replace_with_ptr(prog, ret);

    let replace_ret = match (replace_ret_with_ptr, conv) {
        (false, _) => ChangeReturn::Keep,
        (true, CallingConvention::Win64) => ChangeReturn::Ptr { return_ptr_again: true },
        (true, CallingConvention::Custom) => ChangeReturn::Ptr { return_ptr_again: false },
    };

    AbiChanges {
        replace_param_with_ptr,
        replace_ret,
    }
}

fn win64_replace_with_ptr(prog: &Program, ty: Type) -> bool {
    // TODO win64 return values are weird, they accept "1, 2, 4, 8, 16, 32, or 64 bits"
    //   instead of only byte-sized values
    let layout = Layout::for_type(prog, ty);
    let pass_by_value = [1, 2, 4, 8].contains(&layout.size_bytes);
    !pass_by_value
}

use std::collections::HashMap;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::{Usage, UseInfo};
use crate::mid::ir::{Block, Function, InstructionInfo, Phi, PhiInfo, Program, StackSlot, Type, Value};

///Replace slots and the associated loads and stores with phi values where possible
pub fn slot_to_phi(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let funcs: Vec<Function> = prog.nodes.funcs.iter().map(|(func, _)| func).collect();

    let mut replaced_slot_count = 0;

    //this pass applies to each function separately
    for func in funcs {
        replaced_slot_count += slot_to_phi_fun(prog, &use_info, func);
    }

    println!("slot_to_phi removed {:?} slots", replaced_slot_count);
    replaced_slot_count != 0
}


//TODO this could be replaced by a more efficient data structure
type PhiMap = HashMap<(Block, StackSlot), Phi>;

//TODO this is a complete bruteforce implementation
//  there are lots of way to improve this, but this works for now
fn slot_to_phi_fun(prog: &mut Program, use_info: &UseInfo, func: Function) -> usize {
    let func_info = prog.get_func(func);
    let dom_info = DomInfo::new(prog, func);
    let entry_block = func_info.entry.block;

    //figure out the slots we can replace
    let replaced_slots: Vec<StackSlot> = func_info.slots.iter().copied().filter(|&slot| {
        let inner_ty = prog.get_slot(slot).inner_ty;
        use_info[Value::Slot(slot)].iter().all(|usage| is_load_or_store_addr_with_type(prog, usage, inner_ty))
    }).collect();

    //create all phis
    let mut phi_map: PhiMap = HashMap::new();
    for &slot in &replaced_slots {
        let ty = prog.get_slot(slot).inner_ty;

        for &block in &dom_info.blocks {
            let phi = prog.define_phi(PhiInfo { ty });

            prog.get_block_mut(block).phis.push(phi);
            phi_map.insert((block, slot), phi);
        }
    }

    //fill in phi operands
    for &slot in &replaced_slots {
        //fill in phi operands
        for &block in &dom_info.blocks {
            let block_instr_count = prog.get_block(block).instructions.len();
            let value = get_value_for_slot(prog, &dom_info, &phi_map, entry_block, &replaced_slots, slot, block, block_instr_count);

            prog.get_block_mut(block).terminator.for_each_target_mut(|target| {
                target.phi_values.push(value)
            });
        }

        //TODO what is this for? does this ever make sense? fix this when rewriting slot_to_phi
        //push entry undef values
        let ty = prog.get_slot(slot).inner_ty;
        prog.get_func_mut(func).entry.phi_values.push(Value::Undef(ty));

        let slot_usages = &use_info[Value::Slot(slot)];

        //replace loads
        for &usage in slot_usages {
            match usage {
                Usage::LoadAddr { pos } => {
                    //some assertions
                    let instr_info = prog.get_instr(pos.instr);
                    let addr = unwrap_match!(instr_info, InstructionInfo::Load { addr, .. } => *addr);
                    assert_eq!(Value::Slot(slot), addr);

                    //build value corresponding to this load
                    let load_index = prog.get_block(pos.block).instructions.iter()
                        .position(|&instr| instr == pos.instr).unwrap();

                    let value = get_value_for_slot(prog, &dom_info, &phi_map, entry_block, &replaced_slots, slot, pos.block, load_index);
                    use_info.replace_usages(prog, Value::Instr(pos.instr), value);
                }
                Usage::StoreAddr { pos } => {
                    //some assertions
                    let instr_info = prog.get_instr(pos.instr);
                    let addr = unwrap_match!(instr_info, InstructionInfo::Store { addr, .. } => *addr);
                    assert_eq!(Value::Slot(slot), addr);

                    //nothing to actually do here, we're only replacing loads
                }
                _ => unreachable!("usage type: {:?}", usage),
            }
        }

        //remove loads & stores
        for &usage in slot_usages {
            let pos = unwrap_match!(usage, Usage::LoadAddr { pos } | Usage::StoreAddr { pos } => pos);
            remove_item(&mut prog.get_block_mut(pos.block).instructions, &pos.instr).unwrap();
        }
    }

    //remove the now unused slots
    prog.get_func_mut(func).slots
        .retain(|slot| !replaced_slots.contains(&slot));

    replaced_slots.len()
}

fn is_load_or_store_addr_with_type(prog: &Program, usage: &Usage, expected_ty: Type) -> bool {
    let pos = match usage {
        Usage::LoadAddr { pos } | Usage::StoreAddr { pos } => pos,
        _ => return false,
    };
    let instr = prog.get_instr(pos.instr);
    let ty = unwrap_match!(instr, InstructionInfo::Load { ty, .. } | InstructionInfo::Store{ ty, .. } => *ty);
    ty == expected_ty
}

/// This function is the heart of this pass: it recursively calls itself to figure out the value of
/// a slot at a given program position, inserting phi nodes along the way.
fn get_value_for_slot(
    prog: &mut Program,
    dom_info: &DomInfo,
    phi_map: &PhiMap,
    entry: Block,
    replaced_slots: &Vec<StackSlot>,
    slot: StackSlot,
    block: Block,
    instr_pos: usize,
) -> Value {
    let ty = prog.get_slot(slot).inner_ty;

    //find a matching store in the current block
    for &instr in prog.get_block(block).instructions[0..instr_pos].iter().rev() {
        if let &InstructionInfo::Store { addr, value, ty: _ } = prog.get_instr(instr) {
            if addr == Value::Slot(slot) {
                //if the stored value is a load that will be also replaced by this pass we need to keep recursing
                if let Value::Instr(value_instr) = value {
                    if let &InstructionInfo::Load { addr: Value::Slot(value_slot), ty: _ } = prog.get_instr(value_instr) {
                        if replaced_slots.contains(&value_slot) {
                            //find the block that contains the load
                            let block = *dom_info.blocks.iter().find(|&&block| {
                                prog.get_block(block).instructions.contains(&value_instr)
                            }).unwrap();

                            //find the index of the load in that block
                            let value_index = prog.get_block(block).instructions.iter()
                                .position(|&i| i == value_instr).unwrap();

                            return get_value_for_slot(prog, dom_info, phi_map, entry, replaced_slots, value_slot, block, value_index);
                        }
                    }
                }

                return value;
            }
        }
    }

    //if there is no predecessor the value is just undefined
    if block == entry {
        return Value::Undef(ty);
    }

    //return the corresponding phi value
    Value::Phi(*phi_map.get(&(block, slot)).unwrap())
}

fn remove_item<T: PartialEq>(vec: &mut Vec<T>, item: &T) -> Option<T> {
    vec.iter().position(|elem| elem == item)
        .map(|index| vec.remove(index))
}
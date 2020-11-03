use std::collections::HashMap;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::{Usage, UseInfo};
use crate::mid::ir::{Block, Function, InstructionInfo, Phi, PhiInfo, Program, StackSlot, Value};

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

fn slot_to_phi_fun(prog: &mut Program, use_info: &UseInfo, func: Function) -> usize {
    let func_info = prog.get_func(func);
    let dom_info = DomInfo::new(prog, func);
    let entry = func_info.entry;

    //figure out the slots we can replace
    let replaced_slots: Vec<StackSlot> = func_info.slots.iter().copied().filter(|&slot| {
        use_info[Value::Slot(slot)].iter()
            .all(|usage| matches!(usage, Usage::Addr(_, _)))
    }).collect();

    //iterate over all usages of those slots and build a phi graph for them all at the same time
    //doing this for each slot separately doesn't work because they might end up using each other
    let mut phi_map: PhiMap = HashMap::new();

    for &slot in &replaced_slots {
        let slot_usages = &use_info[Value::Slot(slot)];

        //replace all loads with the actual value
        for &usage in slot_usages {
            if let Usage::Addr(instr, block) = usage {
                let instr_info = prog.get_instr(instr);
                match instr_info {
                    &InstructionInfo::Load { addr } => {
                        debug_assert_eq!(Value::Slot(slot), addr);

                        //found a load, build a value for it and replace it
                        let load_index = prog.get_block(block).instructions.iter()
                            .position(|&i| i == instr).unwrap();

                        let value = build_value_for_slot(prog, &dom_info, &mut phi_map, entry, &replaced_slots, slot, block, load_index);
                        use_info.replace_usages(prog, Value::Instr(instr), value);
                    }
                    &InstructionInfo::Store { addr, .. } => {
                        //nothing to do here, this will be removed later
                        debug_assert_eq!(Value::Slot(slot), addr);
                    }
                    _ => unreachable!("instr type: {:?}", instr_info),
                }
            } else {
                unreachable!("usage type: {:?}", usage);
            }
        }

        //remove the loads and stores
        for &usage in slot_usages {
            if let Usage::Addr(instr, block) = usage {
                remove_item(&mut prog.get_block_mut(block).instructions, &instr).unwrap();
            } else {
                unreachable!("usage type: {:?}", usage)
            }
        }
    }

    //remove the now unused slots
    prog.get_func_mut(func).slots
        .retain(|slot| !replaced_slots.contains(&slot));

    return replaced_slots.len();
}

/// This function is the heart of this pass: it recursively calls itself to figure out the value of
/// a slot at a given program position, inserting phi nodes along the way.
fn build_value_for_slot(
    prog: &mut Program,
    dom_info: &DomInfo,
    phi_map: &mut PhiMap,
    entry: Block,
    replaced_slots: &Vec<StackSlot>,
    slot: StackSlot,
    block: Block,
    instr_pos: usize,
) -> Value {
    let ty = prog.get_slot(slot).inner_ty;

    //find a matching store in the current block
    for &instr in prog.get_block(block).instructions[0..instr_pos].iter().rev() {
        if let &InstructionInfo::Store { addr, value } = prog.get_instr(instr) {
            if addr == Value::Slot(slot) {
                //if the stored value is a load that will be also replaced by this pass we need to keep recursing
                if let Value::Instr(value_instr) = value {
                    if let &InstructionInfo::Load { addr: Value::Slot(value_slot) } = prog.get_instr(value_instr) {
                        if replaced_slots.contains(&value_slot) {
                            //find the block that contains the load
                            let block = *dom_info.blocks.iter().find(|&&block| {
                                prog.get_block(block).instructions.contains(&value_instr)
                            }).unwrap();

                            //find the index of the load in that block
                            let value_index = prog.get_block(block).instructions.iter()
                                .position(|&i| i == value_instr).unwrap();

                            return build_value_for_slot(prog, dom_info, phi_map, entry, replaced_slots, value_slot, block, value_index);
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

    //if this block already has a phi for this slot return it
    if let Some(&phi) = phi_map.get(&(block, slot)) {
        return Value::Phi(phi);
    }

    //otherwise create a new phi and populate it
    //immediately insert it because this phi might be used by itself
    let phi = prog.define_phi(PhiInfo { ty });
    prog.get_block_mut(block).phis.push(phi);
    phi_map.insert((block, slot), phi);

    for pred in dom_info.iter_predecessors(block) {
        let pred_inst_count = prog.get_block(pred).instructions.len();
        let value = build_value_for_slot(prog, dom_info, phi_map, entry, replaced_slots, slot, pred, pred_inst_count);
        prog.get_block_mut(pred).terminator.for_each_target_mut(|target| {
            if target.block == block {
                target.phi_values.push(value);
            }
        })
    }

    Value::Phi(phi)
}

fn remove_item<T: PartialEq>(vec: &mut Vec<T>, item: &T) -> Option<T> {
    vec.iter().position(|elem| elem == item)
        .map(|index| vec.remove(index))
}
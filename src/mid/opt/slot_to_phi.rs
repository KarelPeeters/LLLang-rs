use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::{Usage, UseInfo};
use crate::mid::ir::{Block, Function, InstructionInfo, Phi, PhiInfo, Program, StackSlot, Terminator, Value};

pub fn slot_to_phi(prog: &mut Program) {
    let use_info = UseInfo::new(prog);
    let funcs: Vec<Function> = prog.nodes.funcs.iter().map(|(func, _)| func).collect();

    //TODO figure out a way to skip dead functions here
    // or not, just stick with GC'ing after every pass?

    let mut removed_slot_count = 0;

    for func in funcs {
        let func_info = prog.get_func(func);
        let dom_info = DomInfo::new(prog, func);

        let mut slots: Vec<(StackSlot, bool)> = func_info.slots.iter()
            .map(|&s| (s, true))
            .collect();

        for (slot_index, (slot, keep_slot)) in slots.iter_mut().enumerate() {
            let slot_usages = use_info.get(Value::Slot(*slot));

            if let Some(slot_usages) = slot_usages {
                if slot_usages.iter().all(|u| matches!(u, Usage::Addr(_, _))) {
                    replace_usages_with_phis(prog, *slot, slot_usages, &use_info, &dom_info);
                    *keep_slot = false;
                }
            } else {
                //unused slot, just remove it
                prog.get_func_mut(func).slots.remove(slot_index);
                *keep_slot = false;
            }

            if !*keep_slot {
                removed_slot_count += 1;
            }
        }

        //remove replaced slots
        let mut i = 0;
        prog.get_func_mut(func).slots.retain(|_| {
            let keep = slots[i].1;
            i += 1;
            keep
        })
    }

    println!("slot_to_phi removed {} slots", removed_slot_count);
}

fn find_value_and_declare_phis(prog: &mut Program, slot: StackSlot, phis: &mut Vec<Option<Phi>>, block: Block, from_instr_index: usize, dom_info: &DomInfo) -> Value {
    for &instr in prog.get_block(block).instructions[0..from_instr_index].iter().rev() {
        if let InstructionInfo::Store { addr, value } = prog.get_instr(instr) {
            if *addr == Value::Slot(slot) {
                //we found a matching store!
                return *value;
            }
        }
    }

    //we ran out of instructions, add a phi to this block
    let ty = prog.get_slot(slot).inner_ty;
    let bi = dom_info.block_index(block);

    let phi = match phis[bi] {
        None => {
            let phi = prog.define_phi(PhiInfo { ty });
            prog.get_block_mut(block).phis.push(phi);
            phis[bi] = Some(phi);

            //populate the phi with actual values, found recursively
            for pred in dom_info.iter_predecessors(block) {
                let instr_count = prog.get_block(pred).instructions.len();

                let pred_value = find_value_and_declare_phis(prog, slot, phis, pred, instr_count, dom_info);

                match &mut prog.get_block_mut(pred).terminator {
                    Terminator::Jump { target } => {
                        debug_assert!(target.block == block);
                        target.phi_values.push(pred_value);
                    }
                    Terminator::Branch { targets, .. } => {
                        let mut pushed_any = false;
                        for target in targets {
                            if target.block == block {
                                pushed_any = true;
                                target.phi_values.push(pred_value);
                            }
                        }
                        debug_assert!(pushed_any);
                    }
                    Terminator::Return { .. } => unreachable!(),
                    Terminator::Unreachable => unreachable!(),
                }
            }

            phi
        }
        Some(phi) => {
            phi
        }
    };

    Value::Phi(phi)
}

fn replace_usages_with_phis(prog: &mut Program, slot: StackSlot, slot_usages: &Vec<Usage>, use_info: &UseInfo, dom_info: &DomInfo) {
    let mut phis: Vec<Option<Phi>> = vec![None; dom_info.blocks.len()];

    //first pass, define phi values and replace loads)
    for &usage in slot_usages {
        if let Usage::Addr(instr, block) = usage {
            let instr_info = prog.get_instr(instr);
            match instr_info {
                InstructionInfo::Load { addr } => {
                    debug_assert_eq!(Value::Slot(slot), *addr);
                    let load_index = prog.get_block(block).instructions.iter()
                        .position(|&i| i == instr).unwrap();

                    let value = find_value_and_declare_phis(prog, slot, &mut phis, block, load_index, dom_info);
                    use_info.replace_usages(prog, Value::Instr(instr), value);
                }
                InstructionInfo::Store { addr, value: _ } => {
                    debug_assert_eq!(Value::Slot(slot), *addr);
                }
                _ => unreachable!("instruction: {:?}", instr),
            }
        } else {
            unreachable!("usage: {:?}", usage);
        }
    }

    //second pass, actually remove the loads and stores
    for &usage in slot_usages {
        if let Usage::Addr(instr, block) = usage {
            //remove the instruction from its block
            remove_item(&mut prog.get_block_mut(block).instructions, &instr).unwrap();
        } else {
            panic!("Unexpected usage: {:?}", usage)
        }
    }
}

fn remove_item<T: PartialEq>(vec: &mut Vec<T>, item: &T) -> Option<T> {
    vec.iter().position(|elem| elem == item)
        .map(|index| vec.remove(index))
}
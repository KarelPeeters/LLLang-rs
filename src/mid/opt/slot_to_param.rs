use std::collections::HashMap;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::usage::{InstrOperand, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, Function, InstructionInfo, Parameter, ParameterInfo, Program, Scoped, StackSlot, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::util::internal_iter::InternalIterator;

///Replace slots and the associated loads and stores with block parameters where possible.
#[derive(Debug)]
pub struct SlotToParamPass;

impl ProgramPass for SlotToParamPass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let changed = slot_to_param(prog, ctx);

        PassResult {
            changed,
            preserved_dom_info: true,
            preserved_use_info: !changed,
        }
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

fn slot_to_param(prog: &mut Program, ctx: &mut PassContext) -> bool {
    let use_info = ctx.use_info(prog);
    let funcs: Vec<Function> = prog.nodes.funcs.iter().map(|(func, _)| func).collect();

    let mut replaced_slot_count = 0;

    //this pass applies to each function separately
    for func in funcs {
        let dom_info = ctx.dom_info(prog, func);
        replaced_slot_count += slot_to_param_func(prog, func, &use_info, &dom_info);
    }

    println!("slot_to_param removed {:?} slots", replaced_slot_count);
    replaced_slot_count != 0
}

//TODO this could be replaced by a more efficient data structure
type ParamMap = HashMap<(Block, StackSlot), Parameter>;

//TODO this is a complete bruteforce implementation
//  there are lots of way to improve this, but this works for now
fn slot_to_param_func(prog: &mut Program, func: Function, use_info: &UseInfo, dom_info: &DomInfo) -> usize {
    let func_info = prog.get_func(func);
    let entry_block = func_info.entry;

    // figure out the slots we can replace
    let replaced_slots: Vec<StackSlot> = func_info.slots.iter().copied().filter(|&slot| {
        let inner_ty = prog.get_slot(slot).inner_ty;
        use_info.value_only_used_as_load_store_addr(prog, slot.into(), Some(inner_ty), |_| true)
    }).collect();

    // create all block params
    let mut param_map: ParamMap = HashMap::new();
    for &slot in &replaced_slots {
        let ty = prog.get_slot(slot).inner_ty;

        for &block in dom_info.blocks() {
            if block == entry_block {
                continue;
            }

            let param = prog.define_param(ParameterInfo { ty });

            prog.get_block_mut(block).params.push(param);
            param_map.insert((block, slot), param);
        }
    }

    for &slot in &replaced_slots {
        //fill in block args
        for &block in dom_info.blocks() {
            let block_instr_count = prog.get_block(block).instructions.len();
            let value = get_value_for_slot(prog, &dom_info, &param_map, entry_block, &replaced_slots, slot, block, block_instr_count);

            prog.get_block_mut(block).terminator.targets_mut().for_each(|(target, _)| {
                target.args.push(value)
            });
        }

        //replace loads
        let slot_usages = &use_info[slot];
        for usage in slot_usages {
            match *usage {
                Usage::InstrOperand { pos, usage: InstrOperand::LoadAddr } => {
                    //some assertions
                    let instr_info = prog.get_instr(pos.instr);
                    let addr = unwrap_match!(instr_info, InstructionInfo::Load { addr, .. } => *addr);
                    assert_eq!(addr, slot.into());

                    //build value corresponding to this load
                    let load_index = prog.get_block(pos.block).instructions.iter()
                        .position(|&instr| instr == pos.instr).unwrap();

                    let value = get_value_for_slot(prog, &dom_info, &param_map, entry_block, &replaced_slots, slot, pos.block, load_index);
                    use_info.replace_value_usages(prog, pos.instr.into(), value);
                }
                Usage::InstrOperand { pos, usage: InstrOperand::StoreAddr } => {
                    //some assertions
                    let instr_info = prog.get_instr(pos.instr);
                    let addr = unwrap_match!(instr_info, InstructionInfo::Store { addr, .. } => *addr);
                    assert_eq!(addr, slot.into());

                    //nothing to actually do here, we're only replacing loads
                }
                _ => unreachable!("usage type: {:?}", usage),
            }
        }

        //remove loads & stores
        for usage in slot_usages {
            let pos = unwrap_match!(*usage, Usage::InstrOperand { pos, usage: InstrOperand::LoadAddr | InstrOperand::StoreAddr } => pos);
            remove_item(&mut prog.get_block_mut(pos.block).instructions, &pos.instr).unwrap();
        }
    }

    //remove the now unused slots
    prog.get_func_mut(func).slots
        .retain(|slot| !replaced_slots.contains(slot));

    replaced_slots.len()
}

/// This function is the heart of this pass: it recursively calls itself to figure out the value of
/// a slot at a given program position, inserting block params nodes along the way.
fn get_value_for_slot(
    prog: &mut Program,
    dom_info: &DomInfo,
    param_map: &ParamMap,
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
            if addr == slot.into() {
                //if the stored value is a load that will be also replaced by this pass we need to keep recursing
                if let Value::Scoped(Scoped::Instr(value_instr)) = value {
                    if let &InstructionInfo::Load { addr: Value::Scoped(Scoped::Slot(value_slot)), ty: _ } = prog.get_instr(value_instr) {
                        if replaced_slots.contains(&value_slot) {
                            //find the block that contains the load
                            let block = *dom_info.blocks().iter().find(|&&block| {
                                prog.get_block(block).instructions.contains(&value_instr)
                            }).unwrap();

                            //find the index of the load in that block
                            let value_index = prog.get_block(block).instructions.iter()
                                .position(|&i| i == value_instr).unwrap();

                            return get_value_for_slot(prog, dom_info, param_map, entry, replaced_slots, value_slot, block, value_index);
                        }
                    }
                }

                return value;
            }
        }
    }

    if block == entry {
        // if there is no predecessor the value is just undefined
        Value::undef(ty)
    } else {
        // otherwise return the corresponding block param
        (*param_map.get(&(block, slot)).unwrap()).into()
    }
}

fn remove_item<T: PartialEq>(vec: &mut Vec<T>, item: &T) -> Option<T> {
    vec.iter().position(|elem| elem == item)
        .map(|index| vec.remove(index))
}
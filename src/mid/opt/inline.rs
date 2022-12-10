use itertools::Itertools;

use crate::mid::analyse::use_info::{InstructionPos, Usage, UseInfo};
use crate::mid::ir::{BlockInfo, Function, PhiInfo, Program, Target, Terminator};
use crate::mid::ir::InstructionInfo;
use crate::util::VecExt;

const TINY_FUNCTION_INSTRUCTION_LIMIT: usize = 16;

/// Inline functions that are short or only used rarely.
pub fn inline(prog: &mut Program) -> bool {
    let mut changed = false;

    let use_info = UseInfo::new(prog);
    let mut inlined_calls = vec![];

    // determine which inline actions to take
    for func in prog.nodes.funcs.keys() {
        let usages = &use_info[func];

        // is it even possible to inline?
        if !usages.iter().all(|usage| matches!(usage, Usage::CallTarget { pos: _ })) {
            continue;
        }

        // inline heuristic: small function or only rarely used
        if fn_instruction_count(prog, func) > TINY_FUNCTION_INSTRUCTION_LIMIT && usages.len() > 1 {
            continue;
        }

        // collect calls
        for usage in usages {
            let pos = unwrap_match!(usage, &Usage::CallTarget { pos } => pos);
            let inlined_call = InlinedCall { target: func, pos };
            inlined_calls.push(inlined_call);
        }
    }

    // actually do the inlining
    // TODO actually do all of them, not just the first one
    for &inlined_call in inlined_calls.iter().take(1) {
        run_inline_call(prog, &use_info, inlined_call);
        changed |= true;
    }

    changed
}

#[derive(Debug, Copy, Clone)]
struct InlinedCall {
    target: Function,
    pos: InstructionPos,
}

// TODO splitting the calling block here could invalidate other call_pos block positions
fn run_inline_call(prog: &mut Program, use_info: &UseInfo, inlined_call: InlinedCall) {
    let args = unwrap_match!(prog.get_instr(inlined_call.pos.instr), InstructionInfo::Call { target: _, args } => args.clone());
    let return_ty = prog.get_func(inlined_call.target).func_ty.ret;
    let call_pos = inlined_call.pos;

    // TODO rewrite to enforce fixing slots, using entry, ... with destructing
    let cloned_func = prog.deep_clone_function(inlined_call.target, Some(args.as_slice()));
    let cloned_blocks = prog.collect_blocks(cloned_func.entry.block);

    let return_phi = prog.define_phi(PhiInfo { ty: return_ty });

    // split calling block
    let block_before = call_pos.block;

    let block_before_info = prog.get_block(block_before);
    let call_index = block_before_info.instructions.index_of(&call_pos.instr).unwrap();
    let call_instr = block_before_info.instructions[call_index];

    // replace usages of the returned value
    use_info.replace_value_usages(prog, call_instr.into(), return_phi.into());

    let block_before_info = prog.get_block_mut(block_before);

    // replace old terminator
    let term_before = Terminator::Jump {
        target: cloned_func.entry
    };
    let term_after = std::mem::replace(&mut block_before_info.terminator, term_before);

    // take out "after" instructions
    let instrs_after = block_before_info.instructions.drain(call_index + 1..).collect_vec();
    // remove the call instruction itself
    block_before_info.instructions.pop().unwrap();

    let block_after_info = BlockInfo {
        phis: vec![return_phi],
        instructions: instrs_after,
        terminator: term_after,
    };
    let block_after = prog.define_block(block_after_info);

    // replace returns in the function with jumps to the after block
    for block in cloned_blocks {
        let block_info = prog.get_block_mut(block);
        match block_info.terminator {
            Terminator::Jump { .. } | Terminator::Branch { .. } | Terminator::Unreachable { .. } => {}
            Terminator::Return { value } => {
                block_info.terminator = Terminator::Jump {
                    target: Target {
                        block: block_after,
                        phi_values: vec![value],
                    }
                }
            }
        }
    }

    // take slots into new function
    let calling_func = call_pos.func;
    prog.get_func_mut(calling_func).slots.extend(cloned_func.slots);

    // TODO deconstruct cloned_func to make sure we've used everything
    // TODO all done?
}

fn fn_instruction_count(prog: &Program, func: Function) -> usize {
    let mut count = 0;
    prog.visit_blocks(prog.get_func(func).entry.block, |block| {
        let BlockInfo { phis, instructions, terminator: _ } = prog.get_block(block);
        count += phis.len();
        count += instructions.len();
        count += 1;
    });
    count
}

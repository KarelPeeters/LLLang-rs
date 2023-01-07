use itertools::Itertools;

use crate::mid::analyse::usage::{InstrOperand, InstructionPos, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{BlockInfo, Function, ParameterInfo, Program, Target, Terminator};
use crate::mid::ir::InstructionInfo;
use crate::util::{Never, NeverExt, VecExt};

const TINY_FUNCTION_INSTRUCTION_LIMIT: usize = 16;

/// Inline functions that are short or only used rarely.
pub fn inline(prog: &mut Program) -> bool {
    let mut changes = 0;

    // TODO find a more efficient way to do this, find all inlinable calls and then process all of them at once
    loop {
        let use_info = UseInfo::new(prog);
        let inlined_calls = find_inlined_calls(prog, &use_info);
        for &inlined_call in inlined_calls.iter().take(1) {
            run_inline_call(prog, &use_info, inlined_call);
            changes += 1;
        }

        if inlined_calls.is_empty() {
            break;
        }
    }

    println!("inlined {} calls", changes);

    changes > 0
}

// TODO do something better here, we can still inline direct calls if a function is used as a value
// TODO construct proper call tree and make inlining decisions based on that
fn find_inlined_calls(prog: &Program, use_info: &UseInfo) -> Vec<InlinedCall> {
    let mut inlined_calls = vec![];

    for func in prog.nodes.funcs.keys() {
        let usages = &use_info[func];

        // skip recursive functions and functions used as non-call-targets
        let accept_usage = |usage: &Usage| {
            match usage {
                Usage::InstrOperand { pos, usage: InstrOperand::CallTarget } => pos.func != func,
                _ => false,
            }
        };
        if !usages.iter().all(|usage| accept_usage(usage)) {
            continue;
        }

        // inline heuristic: small function or only rarely used
        if fn_instruction_count(prog, func) > TINY_FUNCTION_INSTRUCTION_LIMIT && usages.len() > 1 {
            continue;
        }

        // collect calls
        for usage in usages {
            let pos = unwrap_match!(usage, &Usage::InstrOperand { pos, usage: InstrOperand::CallTarget } => pos);
            let inlined_call = InlinedCall { target: func, pos };
            inlined_calls.push(inlined_call);
        }
    }

    inlined_calls
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
    let cloned_func = prog.deep_clone_function(inlined_call.target, None)
        .expect("Recursive functions should have been filtered out already");
    let cloned_blocks = prog.collect_blocks(cloned_func.entry);

    let return_param = prog.define_param(ParameterInfo { ty: return_ty });

    // split calling block
    let block_before = call_pos.block;

    let block_before_info = prog.get_block(block_before);
    let call_index = block_before_info.instructions.index_of(&call_pos.instr).unwrap();
    let call_instr = block_before_info.instructions[call_index];

    // replace usages of the returned value
    use_info.replace_value_usages(prog, call_instr.into(), return_param.into());

    let block_before_info = prog.get_block_mut(block_before);

    // replace old terminator
    let term_before = Terminator::Jump {
        target: Target { block: cloned_func.entry, args }
    };
    let term_after = std::mem::replace(&mut block_before_info.terminator, term_before);

    // take out "after" instructions
    let instrs_after = block_before_info.instructions.drain(call_index + 1..).collect_vec();
    // remove the call instruction itself
    block_before_info.instructions.pop().unwrap();

    let block_after_info = BlockInfo {
        params: vec![return_param],
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
                        args: vec![value],
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
    prog.try_visit_blocks(prog.get_func(func).entry, |block| {
        let BlockInfo { params, instructions, terminator: _ } = prog.get_block(block);
        count += params.len();
        count += instructions.len();
        count += 1;
        Never::UNIT
    }).no_err();
    count
}

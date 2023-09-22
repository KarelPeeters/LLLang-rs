use itertools::Itertools;

use crate::mid::analyse::usage::{InstrOperand, InstructionPos, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{BlockInfo, Function, FunctionInfo, ParameterInfo, Program, Target, Terminator};
use crate::mid::ir::InstructionInfo;
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::util::internal_iter::InternalIterator;
use crate::util::VecExt;

const TINY_FUNCTION_INSTRUCTION_LIMIT: usize = 16;

/// Inline functions that are short or only used rarely.
#[derive(Debug)]
pub struct InlinePass;

impl ProgramPass for InlinePass {
    fn run(&self, prog: &mut Program, _: &mut PassContext) -> PassResult {
        let changed = inline(prog);
        PassResult::safe(changed)
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

fn inline(prog: &mut Program) -> bool {
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
    let args = unwrap_match!(
        prog.get_instr(inlined_call.pos.instr),
        InstructionInfo::Call { target: _, args, conv: _ } => args.clone()
    );
    let return_ty = prog.get_func(inlined_call.target).func_ty.ret;
    let call_pos = inlined_call.pos;

    // TODO rewrite to enforce fixing slots, using entry, ... with destructing
    let FunctionInfo { ty: _, func_ty: _, slots: cloned_slots, entry: cloned_entry, debug_name: _ } =
        prog.deep_clone_function(inlined_call.target)
            .expect("Recursive functions should have been filtered out already");
    let cloned_blocks = prog.reachable_blocks(cloned_entry).collect_vec();

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
        target: Target { block: cloned_entry, args }
    };
    let term_after = std::mem::replace(&mut block_before_info.terminator, term_before);

    // take out "after" instructions
    let instrs_after = block_before_info.instructions.drain(call_index + 1..).collect_vec();
    // remove the call instruction itself
    block_before_info.instructions.pop().unwrap();

    let before_name = block_before_info.debug_name.as_ref().map(|name| format!("{}_before", name));
    let after_name = block_before_info.debug_name.as_ref().map(|name| format!("{}_after", name));
    block_before_info.debug_name = before_name;

    let block_after_info = BlockInfo {
        params: vec![return_param],
        instructions: instrs_after,
        terminator: term_after,
        debug_name: after_name,
    };
    let block_after = prog.define_block(block_after_info);

    // replace returns in the function with jumps to the after block
    for block in cloned_blocks {
        let block_info = prog.get_block_mut(block);
        match block_info.terminator {
            Terminator::Jump { .. } | Terminator::Branch { .. } | Terminator::Unreachable | Terminator::LoopForever => {}
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

    // take slots into new function, after adding info to the debug name
    let calling_func = call_pos.func;
    let calling_name = prog.get_func(calling_func).debug_name.as_ref().map_or("_", |s| s).to_owned();
    for &slot in &cloned_slots {
        if let Some(slot_name) = &mut prog.get_slot_mut(slot).debug_name {
            *slot_name = format!("{}.{}", calling_name, slot_name)
        }
    }
    prog.get_func_mut(calling_func).slots.extend(cloned_slots);
}

fn fn_instruction_count(prog: &Program, func: Function) -> usize {
    prog.reachable_blocks(prog.get_func(func).entry).map(|block| {
        let BlockInfo { params, instructions, terminator: _, debug_name: _ } = prog.get_block(block);
        params.len() + instructions.len() + 1
    }).sum()
}

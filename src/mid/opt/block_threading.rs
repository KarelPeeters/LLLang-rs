use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Program, Terminator};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};

#[derive(Debug)]
pub struct BlockThreadingPass;

impl ProgramPass for BlockThreadingPass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let use_info = ctx.use_info(prog);
        let changed = block_threading(prog, &use_info);
        PassResult::safe(changed)
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

fn block_threading(prog: &mut Program, use_info: &UseInfo) -> bool {
    let mut count_skipped = 0;

    for start in use_info.blocks() {
        let mut instructions = vec![];
        let mut curr = start;

        let terminator = loop {
            let curr_info = prog.get_block_mut(curr);

            // steal the instructions
            instructions.append(&mut curr_info.instructions);

            // if we jump to a new block
            if let Terminator::Jump { target } = &curr_info.terminator {
                // and are the only block that does
                // and there are no block args (they are already removed by arg_combine anyway)
                // and it's a different block
                if use_info[target.block].len() == 1 && target.args.is_empty() && target.block != curr {
                    // continue on
                    curr = target.block;
                    count_skipped += 1;
                    continue;
                }
            }

            break std::mem::replace(&mut curr_info.terminator, Terminator::Unreachable);
        };

        let start_info = prog.get_block_mut(start);

        assert!(start_info.instructions.is_empty());
        start_info.instructions = instructions;
        start_info.terminator = terminator;
    }

    println!("block_threading skipped {} jumps", count_skipped);
    count_skipped > 0
}
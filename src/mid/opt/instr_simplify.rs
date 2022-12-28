use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ArithmeticOp, Const, InstructionInfo, LogicalOp, Program, Value};
use crate::mid::util::bit_int::BitInt;
use crate::mid::util::cast_chain::extract_minimal_cast_chain;

/// Simplify local (mostly per-instruction) patterns.
/// We don't need to remove any useless instructions, we can leave that to DCE.
pub fn instr_simplify(prog: &mut Program) -> bool {
    let mut count_replaced = 0;

    let use_info = UseInfo::new(prog);
    let ty_void = prog.ty_void();
    let ty_bool = prog.ty_bool();

    let mut replace = |prog: &mut Program, old: Value, new: Value| {
        count_replaced += use_info.replace_value_usages(prog, old, new);
    };

    for block in use_info.blocks() {
        // We manually iterate over the instructions of the current block, since some optimizations
        //   may change the number of instructions (and hopefully instr_index as well!)
        //   `expected_instr_count` is used as an additional layer of checking.
        let mut instr_index = 0;
        let mut expected_instr_count =prog.nodes.blocks[block].instructions.len();

        while instr_index < expected_instr_count {
            let instr = prog.nodes.blocks[block].instructions[instr_index];
            let instr_info = &prog.nodes.instrs[instr];
            let ty_instr = instr_info.ty(prog);

            match instr_info {
                &InstructionInfo::Load { addr: _, ty } => {
                    if ty == ty_void {
                        replace(prog, instr.into(), Value::Void);
                    }
                }
                InstructionInfo::Store { .. } => {}
                InstructionInfo::Call { .. } => {}

                // most binary simplifications are already handled in SCCP, where they have more information
                // TODO this may change when we add equality to the SCCP lattice (see "combining analysis")
                &InstructionInfo::Arithmetic { kind, left, right } => {
                    match kind {
                        ArithmeticOp::Add => {}
                        ArithmeticOp::Sub => {
                            if left == right {
                                let bits = prog.types[ty_instr].unwrap_int().unwrap();
                                let zero = Const::new(ty_instr, BitInt::zero(bits));
                                replace(prog, instr.into(), zero.into());
                            }
                        }
                        ArithmeticOp::Mul => {}
                        ArithmeticOp::Div(_) => {}
                        ArithmeticOp::Mod(_) => {}
                    };
                }
                &InstructionInfo::Comparison { kind, left, right } => {
                    if left == right {
                        let result = match kind {
                            LogicalOp::Eq => true,
                            LogicalOp::Neq => false,
                            LogicalOp::Gt(_) => false,
                            LogicalOp::Gte(_) => true,
                            LogicalOp::Lt(_) => false,
                            LogicalOp::Lte(_) => true,
                        };

                        let result_const = Const::new(ty_bool, BitInt::from_bool(result));
                        replace(prog, instr.into(), result_const.into());
                    }
                }

                InstructionInfo::TupleFieldPtr { .. } => {}
                InstructionInfo::PointerOffSet { .. } => {}

                &InstructionInfo::Cast { .. } => {
                    let chain = extract_minimal_cast_chain(prog, instr.into());

                    // if this chain is shorter than what we have right now
                    if chain.ops.len() < chain.origin_cast_count {
                        let prog_instrs = &mut prog.nodes.instrs;
                        let prog_types = &mut prog.types;

                        // this iterator construct is similar to scan, but we can get the final value out
                        let mut new_value = chain.inner;
                        let new_instructions = chain.ops.iter().map(|&op| {
                            let instr = prog_instrs.push(op.to_instruction(prog_types, new_value));
                            new_value = instr.into();
                            instr
                        });

                        // insert new instructions
                        let instructions = &mut prog.nodes.blocks[block].instructions;
                        drop(instructions.splice(instr_index..instr_index, new_instructions));

                        // account for newly inserted instructions
                        instr_index += chain.ops.len();
                        expected_instr_count += chain.ops.len();

                        // actually replace the old cast with the outermost new one
                        replace(prog, instr.into(), new_value);
                    }
                }

                InstructionInfo::BlackBox { .. } => {}
            }

            assert_eq!(expected_instr_count, prog.nodes.blocks[block].instructions.len());
            instr_index += 1;
        }
    }

    println!("instr_simplify replaced {} values", count_replaced);
    count_replaced != 0
}


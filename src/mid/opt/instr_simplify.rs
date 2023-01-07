use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ArithmeticOp, ComparisonOp, Const, Expression, ExpressionInfo, InstructionInfo, Program, Value};
use crate::mid::util::bit_int::BitInt;
use crate::mid::util::cast_chain::extract_minimal_cast_chain;

/// Simplify local (mostly single instruction or single expression) patterns.
pub fn instr_simplify(prog: &mut Program) -> bool {
    let mut count_replaced = 0;

    let use_info = UseInfo::new(prog);
    let ty_void = prog.ty_void();

    // simplify instructions
    for block in use_info.blocks() {
        for instr_index in 0..prog.get_block(block).instructions.len() {
            let instr = prog.get_block(block).instructions[instr_index];
            let instr_info = prog.get_instr(instr);

            match *instr_info {
                // TODO replace load/store with undef addr with unreachable terminator
                InstructionInfo::Load { addr: _, ty } => {
                    if ty == ty_void {
                        count_replaced += use_info.replace_value_usages(prog, instr.into(), Value::void());
                    }
                }
                InstructionInfo::Store { .. } => {}
                InstructionInfo::Call { .. } => {}
                InstructionInfo::BlackBox { .. } => {}
            }
        }
    }

    // simplify expressions
    for &expr in use_info.expressions() {
        let new = simplify_expression(prog, expr);
        if new != expr.into() {
            use_info.replace_value_usages(prog, expr.into(), new);
        }
    }

    println!("instr_simplify replaced {} values", count_replaced);
    count_replaced != 0
}

fn simplify_expression(prog: &mut Program, expr: Expression) -> Value {
    let ty_expr = prog.type_of_value(expr.into());

    match *prog.get_expr(expr) {
        // most binary simplifications are already handled in SCCP, where they have more information
        // TODO this may change when we add equality to the SCCP lattice (see "combining analysis")
        ExpressionInfo::Arithmetic { kind, left, right } => {
            match kind {
                ArithmeticOp::Add => {}
                ArithmeticOp::Sub => {
                    if left == right {
                        let bits = prog.types[ty_expr].unwrap_int().unwrap();
                        return Const::new(ty_expr, BitInt::zero(bits)).into();
                    }
                }
                ArithmeticOp::Mul => {}
                ArithmeticOp::Div(_) => {}
                ArithmeticOp::Mod(_) => {}
                ArithmeticOp::And => {}
                ArithmeticOp::Or => {}
                ArithmeticOp::Xor => {}
            };
        }
        ExpressionInfo::Comparison { kind, left, right } => {
            if left == right {
                let result = match kind {
                    ComparisonOp::Eq => true,
                    ComparisonOp::Neq => false,
                    ComparisonOp::Gt(_) => false,
                    ComparisonOp::Gte(_) => true,
                    ComparisonOp::Lt(_) => false,
                    ComparisonOp::Lte(_) => true,
                };

                return prog.const_bool(result).into();
            }
        }
        ExpressionInfo::Cast { .. } => {
            let chain = extract_minimal_cast_chain(prog, expr.into());

            // if this chain is shorter than what we have right now
            if chain.ops.len() < chain.origin_cast_count {
                let new_value = chain.ops.iter().fold(chain.inner, |curr, &op| {
                    let expr_info = op.to_expression(&mut prog.types, curr);
                    prog.define_expr(expr_info).into()
                });
                return new_value;
            }
        }
        ExpressionInfo::TupleFieldPtr { .. } => {}
        ExpressionInfo::PointerOffSet { .. } => {}
    }

    expr.into()
}

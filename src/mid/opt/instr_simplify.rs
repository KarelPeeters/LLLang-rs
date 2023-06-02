use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ArithmeticOp, Block, ComparisonOp, Const, Expression, ExpressionInfo, InstructionInfo, Program, Terminator, Value};
use crate::mid::util::bit_int::BitInt;
use crate::mid::util::cast_chain::extract_minimal_cast_chain;

/// Simplify local (mostly single instruction or single expression) patterns.
/// This also replaced unreachable instructions with a terminator, and removed all following instructions.
// TODO make all of this part of the future uber-SCCP pass
pub fn instr_simplify(prog: &mut Program) -> bool {
    let mut count_replaced = 0;

    let use_info = UseInfo::new(prog);
    let ty_void = prog.ty_void();

    let mut block_unreachable_at: Vec<(Block, usize)> = vec![];

    // simplify instructions
    for block in use_info.blocks() {
        for instr_index in 0..prog.get_block(block).instructions.len() {
            let instr = prog.get_block(block).instructions[instr_index];
            let instr_info = prog.get_instr(instr);

            let mut unreachable = false;

            match *instr_info {
                InstructionInfo::Load { addr, ty } => {
                    if addr.is_const_zero() || addr.is_undef() {
                        unreachable = true;
                    } else if ty == ty_void {
                        count_replaced += use_info.replace_value_usages(prog, instr.into(), Value::void());
                    }
                }
                InstructionInfo::Store { addr, ty: _, value: _ } => {
                    unreachable = addr.is_const_zero() || addr.is_undef();
                }
                InstructionInfo::Call { target, args: _, conv: _ } => {
                    unreachable = target.is_const_zero() || target.is_undef();
                }
                InstructionInfo::BlackBox { .. } => {},
            };

            if unreachable {
                block_unreachable_at.push((block, instr_index));
                break;
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

    // replace unreachable instructions with terminator
    let mut instr_deleted = 0;
    for &(block, index) in &block_unreachable_at {
        let block_info = prog.get_block_mut(block);

        instr_deleted += block_info.instructions[index..].len();

        drop(block_info.instructions.drain(index..));
        block_info.terminator = Terminator::Unreachable;
    }

    println!(
        "instr_simplify replaced {} values and deleted {} instructions in {} blocks",
        count_replaced, instr_deleted, block_unreachable_at.len()
    );
    count_replaced != 0
}

fn simplify_expression(prog: &mut Program, expr: Expression) -> Value {
    let ty_expr = prog.type_of_value(expr.into());

    match *prog.get_expr(expr) {
        // most binary simplifications are already handled in SCCP, where they have more information
        // TODO this may change when we add equality to the SCCP lattice (see "combining analysis")
        ExpressionInfo::Arithmetic { kind, left, right } => {
            let properties = kind.properties();

            // value cancels itself itself
            if left == right && (kind == ArithmeticOp::Sub || kind == ArithmeticOp::Xor) {
                let bits = prog.types[ty_expr].unwrap_int().unwrap();
                return Const::new(ty_expr, BitInt::zero(bits)).into();
            }

            // combine constants
            if right.is_const() && properties.associative {
                if let Value::Expr(left) = left {
                    if let &ExpressionInfo::Arithmetic { kind: left_kind, left: left_left, right: left_right } = prog.get_expr(left) {
                        if left_kind == kind && left_right.is_const() {
                            let new_expr_right = ExpressionInfo::Arithmetic { kind, left: left_right, right };
                            let new_expr_right = prog.define_expr(new_expr_right);

                            let new_expr = ExpressionInfo::Arithmetic { kind, left: left_left, right: new_expr_right.into() };
                            return prog.define_expr(new_expr).into();
                        }
                    }
                }
            }

            // move constants to the right
            if let Some(commuted) = properties.commuted {
                if left.is_const() && !right.is_const() {
                    let new_expr = ExpressionInfo::Arithmetic { kind: commuted, left: right, right: left };
                    return prog.define_expr(new_expr).into();
                }
            }

            // replace -const with +(-const)
            if kind == ArithmeticOp::Sub && right.is_const() {
                let right = right.as_const().unwrap();
                let right_neg = Const::new(right.ty, right.value.negate());
                let new_expr = ExpressionInfo::Arithmetic { kind: ArithmeticOp::Add, left, right: right_neg.into() };
                return prog.define_expr(new_expr).into();
            }
        }
        ExpressionInfo::Comparison { kind, left, right } => {
            let properties = kind.properties();

            // compare value with itself
            if left == right {
                return prog.const_bool(properties.result_self).into();
            }

            // move constants to the right
            if left.is_const() && !right.is_const() {
                let new_expr = ExpressionInfo::Comparison { kind: properties.commuted, left: right, right: left };
                return prog.define_expr(new_expr).into();
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
        ExpressionInfo::PointerOffSet { ty: _, base, index } => {
            if index.is_const_zero() {
                return base;
            }
        }
    }

    expr.into()
}

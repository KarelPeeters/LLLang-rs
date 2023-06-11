use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ArithmeticOp, Block, ComparisonOp, Const, Expression, ExpressionInfo, InstructionInfo, Program, Terminator, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::mid::util::bit_int::BitInt;
use crate::mid::util::cast_chain::extract_minimal_cast_chain;

/// Simplify local (mostly single instruction or single expression) patterns.
/// This also replaces unreachable instructions with a terminator, and removes all following instructions.
#[derive(Debug)]
pub struct InstrSimplifyPass;

impl ProgramPass for InstrSimplifyPass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let use_info = ctx.use_info(prog);
        let changed = instr_simplify(prog, &use_info);
        PassResult::safe(changed)
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

// TODO make all of this part of the future uber-SCCP pass
//   or even better, immediately do these simplifications while adding instructions/expressions
fn instr_simplify(prog: &mut Program, use_info: &UseInfo) -> bool {
    let mut count_replaced = 0;

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
                InstructionInfo::BlackBox { .. } => {}
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
            count_replaced += use_info.replace_value_usages(prog, expr.into(), new);
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

    let mut term_simplified = 0;

    // simplify terminators
    for block in use_info.blocks() {
        // simplify terminator
        if let &Terminator::Branch { cond, ref true_target, ref false_target } = &prog.get_block(block).terminator {
            // convert `branch(!c, a, b) => branch(c, b, a)`
            if let Some(&ExpressionInfo::Comparison { kind, left, right }) = cond.as_expr().map(|expr| prog.get_expr(expr)) {
                if kind == ComparisonOp::Eq && prog.type_of_value(left) == prog.ty_bool() && right.is_const_zero() {
                    let new_terminator = Terminator::Branch { cond: left, true_target: false_target.clone(), false_target: true_target.clone() };
                    prog.get_block_mut(block).terminator = new_terminator;
                    term_simplified += 1;
                }
            }
        }
    }

    println!(
        "instr_simplify replaced {} values, deleted {} instructions in {} blocks and simplified {} terminators",
        count_replaced, instr_deleted, block_unreachable_at.len(), term_simplified,
    );
    count_replaced != 0 || instr_deleted != 0 || !block_unreachable_at.is_empty() || term_simplified != 0
}

fn simplify_expression(prog: &mut Program, expr: Expression) -> Value {
    match *prog.get_expr(expr) {
        // most binary simplifications are already handled in SCCP, where they have more information
        // TODO this may change when we add equality to the SCCP lattice (see "combining analysis")
        ExpressionInfo::Arithmetic { kind, ty, left, right } => {
            let properties = kind.properties();

            // value cancels itself itself
            if left == right && (kind == ArithmeticOp::Sub || kind == ArithmeticOp::Xor) {
                let bits = prog.types[ty].unwrap_int().unwrap();
                return Const::new(ty, BitInt::zero(bits)).into();
            }

            // combine constants
            if right.is_const() && properties.associative {
                if let Value::Expr(left) = left {
                    if let &ExpressionInfo::Arithmetic { kind: left_kind, ty: left_ty, left: left_left, right: left_right } = prog.get_expr(left) {
                        assert_eq!(left_ty, ty);

                        if left_kind == kind && left_right.is_const() {
                            let new_expr_right = ExpressionInfo::Arithmetic { kind, ty, left: left_right, right };
                            let new_expr_right = prog.define_expr(new_expr_right);

                            let new_expr = ExpressionInfo::Arithmetic { kind, ty, left: left_left, right: new_expr_right.into() };
                            return prog.define_expr(new_expr).into();
                        }
                    }
                }
            }

            // TODO do this temporarily, check other simplifications, and only then actually add this to the program
            // move constants to the right
            if let Some(commuted) = properties.commuted {
                if left.is_const() && !right.is_const() {
                    let new_expr = ExpressionInfo::Arithmetic { kind: commuted, ty, left: right, right: left };
                    return prog.define_expr(new_expr).into();
                }
            }

            // replace -const with +(-const)
            if kind == ArithmeticOp::Sub && right.is_const() {
                let right = right.as_const().unwrap();
                let right_neg = Const::new(right.ty, right.value.negate());
                let new_expr = ExpressionInfo::Arithmetic { kind: ArithmeticOp::Add, ty, left, right: right_neg.into() };
                return prog.define_expr(new_expr).into();
            }

            // replace x^true with x==false
            if kind == ArithmeticOp::Xor && ty == prog.ty_bool() && right.is_const() && !right.is_const_zero() {
                let new_expr = ExpressionInfo::Comparison { kind: ComparisonOp::Eq, left, right: prog.const_bool(false).into() };
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

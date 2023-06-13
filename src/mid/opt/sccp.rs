use std::collections::{HashSet, VecDeque};
use std::num::Wrapping;

use indexmap::map::IndexMap;

use crate::mid::analyse::usage::{BlockPos, InstrOperand, InstructionPos, TermOperand, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ArithmeticOp, Block, CastKind, ComparisonOp, Const, Expression, ExpressionInfo, Function, Global, Immediate, Instruction, InstructionInfo, Program, Scoped, Signed, Target, Terminator, Type, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::mid::util::bit_int::{BitInt, UStorage};
use crate::mid::util::lattice::Lattice;
use crate::util::internal_iter::InternalIterator;
use crate::util::zip_eq;

/// Try to prove values are constant and replace them
#[derive(Debug)]
pub struct SccpPass;

impl ProgramPass for SccpPass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let use_info = ctx.use_info(prog);

        let lattice = compute_lattice_map(prog, &use_info);
        let replaced_value_count = apply_lattice_simplifications(prog, &use_info, &lattice);

        println!("sccp replaced {} values", replaced_value_count);
        let changed = replaced_value_count != 0;

        PassResult::safe(changed)
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

type LatticeMap = IndexMap<Value, Lattice>;

fn compute_lattice_map(prog: &Program, use_info: &UseInfo) -> LatticeMap {
    let mut state = State::new(prog, use_info);

    for &func in prog.root_functions.values() {
        state.mark_func_used_as_non_call_target(func);
    }

    state.run();
    state.values
}

fn apply_lattice_simplifications(prog: &mut Program, use_info: &UseInfo, lattice_map: &LatticeMap) -> usize {
    let mut count = 0;

    for (&value, &lattice_value) in lattice_map {
        assert!(value_can_be_tracked(value));
        if let Lattice::Known(cst) = lattice_value {
            assert!(value_allowed_as_known(cst));
        }

        let ty = prog.type_of_value(value);
        if let Some(lattice_value) = lattice_value.as_value_of_type(prog, ty) {
            // TODO properly check for dominance (and everywhere else we're replacing things)
            // TODO remove this quick slot check
            count += use_info.replace_value_usages_if(prog, value, lattice_value, |prog, usage| {
                if let Some(slot) = lattice_value.as_slot() {
                    if let Some(func) = usage.as_dom_pos().ok().and_then(|pos| pos.function()) {
                        // only replace if this slot belongs to this func
                        prog.get_func(func).slots.contains(&slot)
                    } else {
                        // if we don't know where this slot usage is, fail same
                        false
                    }
                } else {
                    // replace all non-slot values
                    true
                }
            });
        }
    }

    count
}

struct State<'a> {
    prog: &'a Program,
    use_info: &'a UseInfo,

    func_returns: IndexMap<Function, Lattice>,
    values: LatticeMap,

    todo: VecDeque<Todo>,
    funcs_reachable: HashSet<Function>,
    blocks_reachable: HashSet<Block>,
    expr_visited: HashSet<Expression>,
}

#[derive(Debug)]
enum Todo {
    FuncReachable(Function),
    BlockReachable(BlockPos),

    ValueChanged(Value),
    FuncReturnChanged(Function),
}

fn value_can_be_tracked(value: Value) -> bool {
    matches!(value, Value::Scoped(Scoped::Param(_) | Scoped::Instr(_)) | Value::Expr(_))
}

fn value_allowed_as_known(value: Value) -> bool {
    matches!(value, Value::Global(_) | Value::Immediate(Immediate::Const(_)) | Value::Scoped(Scoped::Slot(_)))
}

impl<'a> State<'a> {
    fn new(prog: &'a Program, use_info: &'a UseInfo) -> Self {
        State {
            prog,
            use_info,
            func_returns: Default::default(),
            values: Default::default(),
            todo: Default::default(),
            funcs_reachable: Default::default(),
            blocks_reachable: Default::default(),
            expr_visited: Default::default(),
        }
    }

    fn run(&mut self) {
        let prog = self.prog;

        while let Some(curr) = self.todo.pop_front() {
            match curr {
                Todo::FuncReachable(func) => {
                    if self.funcs_reachable.insert(func) {
                        // mark entry block reachable
                        let entry = prog.get_func(func).entry;
                        let entry_pos = BlockPos { func, block: entry };
                        self.todo.push_back(Todo::BlockReachable(entry_pos));
                    }
                }
                Todo::BlockReachable(pos) => {
                    if self.blocks_reachable.insert(pos.block) {
                        self.visit_new_block(pos);
                    }
                }
                Todo::ValueChanged(value) => {
                    for usage in &self.use_info[value] {
                        self.update_value_usage(value, usage);
                    }
                }
                Todo::FuncReturnChanged(func) => {
                    let return_value = self.eval_func_return(func);

                    // update the value of call instructions with this func as the target
                    for usage in &self.use_info[func] {
                        if let Usage::InstrOperand { pos, usage: InstrOperand::CallTarget } = *usage {
                            if self.reachable(pos.instr) {
                                self.merge_value(pos.instr.into(), return_value);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Assuming the lattice value corresponding to `value` has changed, update the given `usage`.
    /// We need to be careful to only do this for usages that have already been marked as reachable.
    fn update_value_usage(&mut self, value: Value, usage: &Usage) {
        let prog = self.prog;

        match *usage {
            Usage::RootFunction(_) => unreachable!(
                "{:?} used as {:?} should never change, but changed to {:?}",
                value, usage, self.eval(value)
            ),

            Usage::InstrOperand { pos, usage: _ } => {
                if self.reachable(pos.instr) {
                    self.visit_instr(pos.instr);
                }
            }

            Usage::ExprOperand { expr, usage: _ } => {
                if self.expr_visited.contains(&expr) {
                    self.visit_expr(expr);
                }
            }

            Usage::TermOperand { pos, usage: term_usage } => {
                if self.blocks_reachable.contains(&pos.block) {
                    let terminator = &self.prog.get_block(pos.block).terminator;

                    match term_usage {
                        TermOperand::BranchCond => {
                            let (&cond, true_target, false_target) = unwrap_match!(
                                terminator,
                                Terminator::Branch { cond, true_target, false_target } => (cond, true_target, false_target)
                            );
                            self.visit_branch(pos, cond, true_target, false_target)
                        }
                        TermOperand::ReturnValue => {
                            let value = self.eval(value);
                            self.merge_func_return(pos.func, value);
                        }
                        TermOperand::TargetArg { kind, index } => {
                            let target = kind.get_target(terminator);
                            let param = prog.get_block(target.block).params[index];
                            let value = self.eval(value);
                            self.merge_value(param.into(), value);
                        }
                    }
                }
            }
        }
    }

    /// Visit `block` for the first time.
    fn visit_new_block(&mut self, block_pos: BlockPos) {
        let prog = self.prog;
        let block_info = prog.get_block(block_pos.block);

        // visit each instr
        for (instr_index, &instr) in block_info.instructions.iter().enumerate() {
            let instr_pos = InstructionPos { func: block_pos.func, block: block_pos.block, instr, instr_index };
            assert!(!self.reachable(instr));

            // evaluate the instruction
            self.visit_instr(instr);

            // mark each usage in this instruction
            //  visit_instr already does this for most instructions, but not necessarily all of them
            prog.get_instr(instr).operands().for_each(|(value, usage)| {
                let usage = Usage::InstrOperand { pos: instr_pos, usage };
                self.mark_usage(value, usage);
            });
        }

        // visit terminator
        match block_info.terminator {
            Terminator::Jump { ref target } =>
                self.visit_target(block_pos, target),
            Terminator::Branch { cond, ref true_target, ref false_target } =>
                self.visit_branch(block_pos, cond, true_target, false_target),
            Terminator::Return { value } => {
                let value = self.eval(value);
                self.merge_func_return(block_pos.func, value);
            }
            Terminator::Unreachable => {}
            Terminator::LoopForever => {}
        }
    }

    fn visit_branch(&mut self, block_pos: BlockPos, cond: Value, true_target: &Target, false_target: &Target) {
        let cond = self.eval(cond);
        let (visit_true, visit_false) = evaluate_branch_condition(cond);

        if visit_true {
            self.visit_target(block_pos, true_target);
        }
        if visit_false {
            self.visit_target(block_pos, false_target);
        }
    }

    fn visit_target(&mut self, from: BlockPos, target: &Target) {
        let prog = self.prog;

        // mark block reachable
        let pos = BlockPos { func: from.func, block: target.block };
        self.todo.push_back(Todo::BlockReachable(pos));

        // merge phi values
        let target_block_info = prog.get_block(target.block);
        for (&param, &arg) in zip_eq(&target_block_info.params, &target.args) {
            let arg = self.eval(arg);
            self.merge_value(param.into(), arg);
        }
    }

    fn visit_instr(&mut self, instr: Instruction) {
        let prog = self.prog;
        let instr_info = prog.get_instr(instr);

        let result = match *instr_info {
            InstructionInfo::Load { addr, ty: _ } => {
                // loading from undef returns undef
                // TODO maybe replace with unreachable instead?
                //   => return bool "unreachable" and stop visiting instructions & terminator
                self.eval(addr).map_known(|value| {
                    // loading from null returns undef
                    if value.is_const_zero() {
                        Lattice::Undef
                    } else {
                        Lattice::Overdef
                    }
                })
            }

            InstructionInfo::Call { target, ref args, conv: _ } => {
                self.eval_as_call_target(target).map_known(|target| {
                    if let Some(target) = target.as_func() {
                        // mark reachable
                        self.todo.push_back(Todo::FuncReachable(target));

                        // merge in arguments
                        let target_info = prog.get_func(target);
                        let params = &prog.get_block(target_info.entry).params;
                        for (&param, &arg) in zip_eq(params, args) {
                            let arg = self.eval(arg);
                            self.merge_value(param.into(), arg);
                        }

                        // get return
                        self.eval_func_return(target)
                    } else {
                        Lattice::Overdef
                    }
                })
            }

            // void return values
            InstructionInfo::Store { .. } => Lattice::Undef,
            InstructionInfo::BlackHole { .. } => Lattice::Undef,
            InstructionInfo::MemBarrier { .. } => Lattice::Undef,
        };

        self.merge_value(instr.into(), result);
    }

    /// Update the value for the given expression, either because we are visiting it for the first time
    /// or because one of the operands has changed.
    fn visit_expr(&mut self, expr: Expression) {
        let result = self.eval_expr(expr);
        self.merge_value(expr.into(), result);
    }

    /// Evaluate the given expression. Should only be used in `visit_expr` or for debugging.
    fn eval_expr(&mut self, expr: Expression) -> Lattice {
        let prog = self.prog;
        let expr_info = prog.get_expr(expr);

        match *expr_info {
            ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
                // just always assume overdef, maybe this will change when we add const pointers
                self.eval(base).map_known(|_| Lattice::Overdef)
            }
            ExpressionInfo::PointerOffSet { ty: _, base, index: _ } => {
                // just always assume overdef, maybe this will change when we add const pointers
                self.eval(base).map_known(|_| Lattice::Overdef)
            }
            ExpressionInfo::Arithmetic { kind, ty: _, left, right } => {
                // TODO test whether this correct handles all of the edge cases in mul and div
                self.eval_binary(left, right, |ty, left, right| {
                    let left_unsigned = Wrapping(left.unsigned());
                    let right_unsigned = Wrapping(right.unsigned());

                    let result_full = match kind {
                        // we can choose either, the result would be the same
                        ArithmeticOp::Add => (left_unsigned + right_unsigned).0,
                        ArithmeticOp::Sub => (left_unsigned - right_unsigned).0,
                        ArithmeticOp::Mul => (left_unsigned * right_unsigned).0,
                        ArithmeticOp::And => (left_unsigned & right_unsigned).0,
                        ArithmeticOp::Or => (left_unsigned | right_unsigned).0,
                        ArithmeticOp::Xor => (left_unsigned ^ right_unsigned).0,
                        ArithmeticOp::Div(signed) => return eval_div_mod(ty, signed, left, right).0,
                        ArithmeticOp::Mod(signed) => return eval_div_mod(ty, signed, left, right).1,
                    };

                    let bits = left.bits();
                    let result = BitInt::from_unsigned(bits, result_full & BitInt::mask(bits)).unwrap();
                    Lattice::Known(Const::new(ty, result).into())
                })
            }
            ExpressionInfo::Comparison { kind, left, right } => {
                self.eval_binary(left, right, |_, left, right| {
                    let result_bool = match kind {
                        ComparisonOp::Eq => left == right,
                        ComparisonOp::Neq => left != right,

                        ComparisonOp::Gt(Signed::Signed) => left.signed() > right.signed(),
                        ComparisonOp::Gte(Signed::Signed) => left.signed() >= right.signed(),
                        ComparisonOp::Lt(Signed::Signed) => left.signed() < right.signed(),
                        ComparisonOp::Lte(Signed::Signed) => left.signed() <= right.signed(),

                        ComparisonOp::Gt(Signed::Unsigned) => left.unsigned() > right.unsigned(),
                        ComparisonOp::Gte(Signed::Unsigned) => left.unsigned() >= right.unsigned(),
                        ComparisonOp::Lt(Signed::Unsigned) => left.unsigned() < right.unsigned(),
                        ComparisonOp::Lte(Signed::Unsigned) => left.unsigned() <= right.unsigned(),
                    };

                    let result = BitInt::from_bool(result_bool);
                    Lattice::Known(Const::new(prog.ty_bool(), result).into())
                })
            }
            ExpressionInfo::Cast { ty, kind, value } => {
                // check that both are integer types, since that's the only thing cast supports for now
                let old_bits = prog.get_type(prog.type_of_value(value)).unwrap_int().unwrap();
                let new_bits = prog.get_type(ty).unwrap_int().unwrap();

                self.eval(value).map_known_const(|cst| {
                    assert_eq!(cst.value.bits(), old_bits);

                    let result = match kind {
                        CastKind::IntTruncate => {
                            // cannot overflow, we just masked
                            let mask = BitInt::mask(new_bits);
                            BitInt::from_unsigned(new_bits, cst.value.unsigned() & mask).unwrap()
                        }
                        CastKind::IntExtend(Signed::Signed) => {
                            // cannot overflow, we just sign-extended for a signed value
                            BitInt::from_signed(new_bits, cst.value.signed()).unwrap()
                        }
                        CastKind::IntExtend(Signed::Unsigned) => {
                            // cannot overflow, we just zero-extended for an unsigned value
                            BitInt::from_unsigned(new_bits, cst.value.unsigned()).unwrap()
                        }
                    };

                    Lattice::Known(Const::new(ty, result).into())
                })
            }
            // we can't propagate any info
            ExpressionInfo::Obscure { ty: _, value: _ } => Lattice::Overdef,
        }
    }

    fn eval_binary(
        &mut self,
        left: Value,
        right: Value,
        handle_const: impl Fn(Type, BitInt, BitInt) -> Lattice,
    ) -> Lattice {
        match (self.eval(left), self.eval(right)) {
            (Lattice::Undef, _) | (_, Lattice::Undef) => Lattice::Undef,

            (Lattice::Known(Value::Immediate(Immediate::Const(left))), Lattice::Known(Value::Immediate(Immediate::Const(right)))) => {
                assert_eq!(left.ty, right.ty);
                let ty = left.ty;
                assert_eq!(left.value.bits(), right.value.bits());
                handle_const(ty, left.value, right.value)
            }

            // TODO sometimes this can be inferred as well, eg "0 * x" or "x == x"
            _ => Lattice::Overdef,
        }
    }

    fn mark_func_used_as_non_call_target(&mut self, func: Function) {
        let prog = self.prog;

        // mark func as reachable
        self.todo.push_back(Todo::FuncReachable(func));

        // mark params as overdef
        let params = &prog.get_block(prog.get_func(func).entry).params;
        for &param in params {
            self.merge_value(param.into(), Lattice::Overdef);
        }
    }

    fn mark_usage(&mut self, value: Value, usage: Usage) {
        if let Some(func) = value.as_func() {
            if !matches!(usage, Usage::InstrOperand { pos: _, usage: InstrOperand::CallTarget }) {
                self.mark_func_used_as_non_call_target(func);
            }
        }
    }

    /// Look up `value` without any handling of special values.
    fn eval_lookup(&self, value: Value) -> Lattice {
        assert!(value_can_be_tracked(value));
        *self.values.get(&value).unwrap_or(&Lattice::Undef)
    }

    /// General version [eval] that makes the **worst** case assumption that
    /// the corresponding usage is **not** a call target.
    fn eval(&mut self, value: Value) -> Lattice {
        if let Value::Global(Global::Func(func)) = value {
            self.mark_func_used_as_non_call_target(func);
        }

        // we've already handled the function case, now proceed as if it's not a call target
        self.eval_as_call_target(value)
    }

    /// Version of [eval] that assumes the corresponding usage is a call target.
    fn eval_as_call_target(&mut self, value: Value) -> Lattice {
        match value {
            Value::Immediate(Immediate::Void) | Value::Immediate(Immediate::Undef(_)) => Lattice::Undef,

            Value::Immediate(Immediate::Const(_)) => Lattice::Known(value),
            Value::Global(_) => Lattice::Known(value),

            Value::Scoped(scoped) => {
                match scoped {
                    Scoped::Param(_) | Scoped::Instr(_) => self.eval_lookup(value),
                    Scoped::Slot(_) => Lattice::Known(value),
                }
            }

            Value::Expr(expr) => {
                if self.expr_visited.insert(expr) {
                    self.visit_expr(expr);

                    // evaluate all expression operands so they have a chance to be optimized
                    //   visit_expr already evaluates most of them, but is not guaranteed to
                    self.prog.get_expr(expr).operands().for_each(|(operand, _)| {
                        self.eval(operand);
                    });
                }
                *self.values.get(&value).unwrap()
            }
        }
    }

    fn eval_func_return(&self, func: Function) -> Lattice {
        *self.func_returns.get(&func).unwrap_or(&Lattice::Undef)
    }

    fn merge_value(&mut self, value: Value, new: Lattice) {
        let prog = self.prog;

        // don't bother with void values
        if prog.ty_void() == prog.type_of_value(value) {
            return;
        };

        let prev = self.eval_lookup(value);
        let next = Lattice::merge(prev, new);

        self.values.insert(value, next);

        if prev != next {
            self.todo.push_back(Todo::ValueChanged(value));
        }
    }

    fn merge_func_return(&mut self, func: Function, new: Lattice) {
        // TODO combine with merge_value or at least ensure they work the same

        let prev = self.eval_func_return(func);
        let next = Lattice::merge(prev, new);
        self.func_returns.insert(func, next);

        if prev != next {
            self.todo.push_back(Todo::FuncReturnChanged(func));
        }
    }

    fn reachable(&self, instr: Instruction) -> bool {
        self.values.contains_key(&Value::from(instr))
    }
}

/// Returns a tuple `(true_reachable, false_reachable)` for a branch on the given condition
fn evaluate_branch_condition(cond: Lattice) -> (bool, bool) {
    match cond {
        Lattice::Undef => {
            // undefined behaviour, don't mark anything
            (false, false)
        }
        Lattice::Known(cond) => {
            if let Some(cond) = cond.as_const().and_then(|cst| cst.as_bool()) {
                // if this is an actual boolean const we can fully evaluate it
                (cond, !cond)
            } else {
                // otherwise consider this overdefined
                (true, true)
            }
        }
        Lattice::Overdef => {
            // both could be taken
            (true, true)
        }
    }
}

fn eval_div_mod(ty: Type, signed: Signed, left: BitInt, right: BitInt) -> (Lattice, Lattice) {
    if right.is_zero() {
        return (Lattice::Undef, Lattice::Undef);
    }

    let left_signed = Wrapping(left.signed());
    let left_unsigned = Wrapping(left.unsigned());
    let right_signed = Wrapping(right.signed());
    let right_unsigned = Wrapping(right.unsigned());

    let result_full = match signed {
        Signed::Signed => ((left_signed / right_signed).0 as UStorage, (left_signed % right_signed).0 as UStorage),
        Signed::Unsigned => ((left_unsigned / right_unsigned).0, (left_unsigned % right_unsigned).0),
    };

    let bits = left.bits();
    let mask = BitInt::mask(bits);
    let map = |x: UStorage| -> Lattice {
        let bit_int = BitInt::from_unsigned(bits, x & mask).unwrap();
        Lattice::Known(Const::new(ty, bit_int).into())
    };

    (map(result_full.0), map(result_full.1))
}
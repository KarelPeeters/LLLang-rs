use std::collections::{HashSet, VecDeque};
use std::num::Wrapping;

use indexmap::map::IndexMap;

use crate::mid::analyse::use_info::{for_each_usage_in_instr, InstructionPos, TargetKind, Usage, UseInfo};
use crate::mid::ir::{ArithmeticOp, Block, CastKind, ComparisonOp, Const, Function, Immediate, Instruction, InstructionInfo, Program, Scoped, Signed, Target, Terminator, Type, Value};
use crate::mid::util::bit_int::{BitInt, UStorage};
use crate::mid::util::lattice::Lattice;
use crate::util::zip_eq;

///Try to prove values are constant and replace them
pub fn sccp(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);

    let lattice = compute_lattice_map(prog, &use_info);
    let replaced_value_count = apply_lattice_simplifications(prog, &use_info, &lattice);

    println!("sccp replaced {} values", replaced_value_count);
    replaced_value_count != 0
}

#[derive(Default)]
struct LatticeMap {
    func_returns: IndexMap<Function, Lattice>,
    values: IndexMap<Value, Lattice>,
}

fn value_can_be_tracked(value: Value) -> bool {
    matches!(value, Value::Scoped(Scoped::Param(_) | Scoped::Phi(_) | Scoped::Instr(_)))
}

fn value_allowed_as_known(value: Value) -> bool {
    matches!(value, Value::Global(_) | Value::Immediate(Immediate::Const(_)))
}

impl LatticeMap {
    fn eval(&self, value: Value) -> Lattice {
        match value {
            Value::Immediate(Immediate::Void) | Value::Immediate(Immediate::Undef(_)) => Lattice::Undef,

            Value::Immediate(Immediate::Const(_)) => Lattice::Known(value),
            Value::Global(_) => Lattice::Known(value),

            Value::Scoped(scoped) => {
                match scoped {
                    Scoped::Param(_) | Scoped::Phi(_) | Scoped::Instr(_) => {
                        assert!(value_can_be_tracked(value));
                        *self.values.get(&value).unwrap_or(&Lattice::Undef)
                    }
                    // TODO should we track slots as known?
                    Scoped::Slot(_) => Lattice::Overdef,
                }
            }
        }
    }

    fn merge_value(&mut self, prog: &Program, todo: &mut VecDeque<Todo>, value: Value, new: Lattice) {
        assert!(value_can_be_tracked(value));

        // any void value can be treated as undef, this is a good central place to do it
        let new = if prog.ty_void() == prog.type_of_value(value) {
            Lattice::Undef
        } else {
            new
        };

        let prev = self.eval(value);
        let next = Lattice::merge(prev, new);

        // TODO if next is undef remove or just don't insert instead
        self.values.insert(value, next);

        if prev != next {
            todo.push_back(Todo::ValueUsers(value));
        }
    }

    fn eval_func_return(&self, func: Function) -> Lattice {
        *self.func_returns.get(&func).unwrap_or(&Lattice::Undef)
    }

    fn merge_func_return(&mut self, todo: &mut VecDeque<Todo>, func: Function, new: Lattice) {
        let prev = self.eval_func_return(func);
        let next = Lattice::merge(prev, new);
        self.func_returns.insert(func, next);

        if prev != next {
            todo.push_back(Todo::FuncReturnUsers(func));
        }
    }

    fn reachable(&self, value: impl Into<Value>) -> bool {
        self.values.contains_key(&value.into())
    }
}

enum Todo {
    FunctionInit(Function),
    BlockInit(Function, Block),
    ValueUsers(Value),
    FuncReturnUsers(Function),
}

fn compute_lattice_map(prog: &mut Program, use_info: &UseInfo) -> LatticeMap {
    let mut map = LatticeMap::default();

    let mut todo = VecDeque::new();
    todo.push_back(Todo::FunctionInit(prog.main));

    let mut funcs_reachable = HashSet::new();
    let mut blocks_reachable = HashSet::new();

    //TODO move this loop body into a separate function
    while let Some(curr) = todo.pop_front() {
        match curr {
            Todo::FunctionInit(func) => {
                if funcs_reachable.insert(func) {
                    update_target_reachable(prog, &mut map, &mut todo, func, &prog.get_func(func).entry);
                }
            }
            Todo::BlockInit(func, block) => {
                if blocks_reachable.insert(block) {
                    let block_info = prog.get_block(block);

                    //visit each instr
                    for (instr_index, &instr) in block_info.instructions.iter().enumerate() {
                        visit_instr(prog, &mut map, &mut todo, instr);
                        let pos = InstructionPos { func, block, instr, instr_index };

                        //since it's the first time we check for usage of functions as generic operands
                        for_each_usage_in_instr(pos, prog.get_instr(instr), |value, usage| {
                            if let Some(func) = value.as_func() {
                                if !matches!(usage, Usage::CallTarget {..}) {
                                    // mark function parameters as overdefined
                                    for &param in &prog.get_func(func).params {
                                        map.values.insert(param.into(), Lattice::Overdef);
                                    }
                                }
                            }
                        });
                    }

                    //visit terminator
                    match &block_info.terminator {
                        Terminator::Jump { target } => {
                            update_target_reachable(prog, &mut map, &mut todo, func, target);
                        }
                        Terminator::Branch { cond, true_target, false_target } =>
                            visit_branch(prog, &mut map, &mut todo, func, cond, true_target, false_target),
                        &Terminator::Return { value } => {
                            map.merge_func_return(&mut todo, func, map.eval(value))
                        }
                        Terminator::Unreachable => {
                            //nothing to visit
                        }
                    }
                }
            }
            Todo::ValueUsers(value) => {
                // make sure to only visit usages that are alive (ie. have been visited already)

                for &usage in &use_info[value] {
                    match usage {
                        Usage::Main =>
                            unreachable!("This value should never change: {:?}, but changed to {:?}", usage, map.eval(value)),

                        // instructions
                        // TODO group all instruction operand usages together
                        Usage::LoadAddr { pos }
                        | Usage::StoreAddr { pos } | Usage::StoreValue { pos }
                        | Usage::CallTarget { pos }
                        | Usage::TupleFieldPtrBase { pos }
                        | Usage::ArrayIndexPtrBase { pos } | Usage::ArrayIndexPtrIndex { pos }
                        | Usage::BinaryOperandLeft { pos } | Usage::BinaryOperandRight { pos }
                        | Usage::CastValue { pos } | Usage::BlackBoxValue { pos } => {
                            if map.reachable(pos.instr) {
                                visit_instr(prog, &mut map, &mut todo, pos.instr);
                            }
                        }

                        Usage::TargetPhiValue { target_kind, phi_index } => {
                            let reachable = match target_kind {
                                TargetKind::EntryFrom(func) => funcs_reachable.contains(&func),
                                TargetKind::JumpFrom(pos) | TargetKind::BranchTrueFrom(pos) | TargetKind::BranchFalseFrom(pos) => {
                                    blocks_reachable.contains(&pos.block)
                                }
                            };

                            if reachable {
                                let target = target_kind.get_target(prog);

                                let phi = prog.get_block(target.block).phis[phi_index];
                                let new_value = map.eval(target.phi_values[phi_index]);

                                map.merge_value(prog, &mut todo, phi.into(), new_value)
                            }
                        }
                        Usage::CallArgument { pos, index } => {
                            if map.reachable(pos.instr) {
                                match prog.get_instr(pos.instr) {
                                    InstructionInfo::Call { target, args } => {
                                        if let Some(target) = target.as_func() {
                                            //merge in argument
                                            let param = prog.get_func(target).params[index];
                                            map.merge_value(prog, &mut todo, param.into(), map.eval(args[index]));
                                        } else {
                                            //nothing to do here
                                        }
                                    }
                                    _ => unreachable!()
                                }
                            }
                        }
                        Usage::BranchCond { pos } => {
                            if blocks_reachable.contains(&pos.block) {
                                match &prog.get_block(pos.block).terminator {
                                    Terminator::Branch { cond, true_target, false_target } => {
                                        visit_branch(prog, &mut map, &mut todo, pos.func, cond, true_target, false_target)
                                    }
                                    _ => unreachable!()
                                }
                            }
                        }
                        Usage::ReturnValue { pos } => {
                            if blocks_reachable.contains(&pos.block) {
                                match &prog.get_block(pos.block).terminator {
                                    &Terminator::Return { value } => {
                                        //merge in return value
                                        map.merge_func_return(&mut todo, pos.func, map.eval(value))
                                    }
                                    _ => unreachable!()
                                }
                            }
                        }
                    }
                }
            }
            Todo::FuncReturnUsers(func) => {
                let return_lattice = map.eval_func_return(func);

                for &usage in &use_info[func] {
                    if let Usage::CallTarget { pos } = usage {
                        if map.reachable(pos.instr) {
                            map.merge_value(prog, &mut todo, pos.instr.into(), return_lattice);
                            todo.push_back(Todo::ValueUsers(pos.instr.into()))
                        }
                    }
                }
            }
        }
    }

    map
}

fn visit_branch(
    prog: &Program,
    map: &mut LatticeMap,
    todo: &mut VecDeque<Todo>,
    func: Function,
    cond: &Value,
    true_target: &Target,
    false_target: &Target,
) {
    let cond = map.eval(*cond);
    let (visit_true, visit_false) = evaluate_branch_condition(cond);

    if visit_true {
        update_target_reachable(prog, map, todo, func, true_target);
    }
    if visit_false {
        update_target_reachable(prog, map, todo, func, false_target);
    }
}

///Returns a tuple `(true_reachable, false_reachable)` for a branch on the given condition
fn evaluate_branch_condition(cond: Lattice) -> (bool, bool) {
    match cond {
        Lattice::Undef => {
            //undefined behaviour, don't mark anything
            (false, false)
        }
        Lattice::Known(cond) => {
            if let Some(cond) = cond.as_const().and_then(|cst| cst.as_bool()) {
                //if this is an actual boolean const we can fully evaluate it
                (cond, !cond)
            } else {
                //otherwise consider this overdefined
                (true, true)
            }
        }
        Lattice::Overdef => {
            //both could be taken
            (true, true)
        }
    }
}

fn update_target_reachable(prog: &Program, map: &mut LatticeMap, todo: &mut VecDeque<Todo>, func: Function, target: &Target) {
    //mark block reachable
    todo.push_back(Todo::BlockInit(func, target.block));

    //merge phi values
    let target_block_info = prog.get_block(target.block);
    for (&phi, &phi_value) in zip_eq(&target_block_info.phis, &target.phi_values) {
        map.merge_value(prog, todo, phi.into(), map.eval(phi_value));
    }
}

fn visit_instr(prog: &Program, map: &mut LatticeMap, todo: &mut VecDeque<Todo>, instr: Instruction) {
    let instr_info = prog.get_instr(instr);

    let result = match instr_info {
        &InstructionInfo::Load { addr, ty: _ } => {
            // loading from undef returns undef
            // TODO maybe replace with unreachable instead?
            map.eval(addr).map_known(|value| {
                // loading from null returns undef
                if value.is_const_zero() {
                    Lattice::Undef
                } else {
                    Lattice::Overdef
                }
            })
        }
        &InstructionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
            // just always assume overdef, maybe this will change when we add const pointers
            map.eval(base).map_known(|_| Lattice::Overdef)
        }
        &InstructionInfo::PointerOffSet { ty: _, base, index: _ } => {
            // just always assume overdef, maybe this will change when we add const pointers
            map.eval(base).map_known(|_| Lattice::Overdef)
        }
        // this instruction doesn't have a return value, so we can just use anything we want
        InstructionInfo::Store { .. } => Lattice::Undef,
        &InstructionInfo::Call { target, ref args } => {
            map.eval(target).map_known(|target| {
                if let Some(target) = target.as_func() {
                    //mark reachable
                    todo.push_back(Todo::FunctionInit(target));

                    //merge in arguments
                    let target_info = prog.get_func(target);
                    for (&param, &arg) in zip_eq(&target_info.params, args) {
                        map.merge_value(prog, todo, param.into(), map.eval(arg))
                    }

                    //get return
                    map.eval_func_return(target)
                } else {
                    Lattice::Overdef
                }
            })
        }
        &InstructionInfo::Arithmetic { kind, left, right } => {
            // TODO test whether this correct handles all of the edge cases in mul and div
            eval_binary(map, left, right, |ty, left, right| {
                let left_signed = Wrapping(left.signed());
                let right_signed = Wrapping(right.signed());
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

                    //TODO should x/0 and x%0 be undefined?
                    ArithmeticOp::Div(Signed::Signed) => (left_signed / right_signed).0 as UStorage,
                    ArithmeticOp::Mod(Signed::Signed) => (left_signed % right_signed).0 as UStorage,

                    ArithmeticOp::Div(Signed::Unsigned) => (left_unsigned / right_unsigned).0,
                    ArithmeticOp::Mod(Signed::Unsigned) => (left_unsigned % right_unsigned).0,
                };

                // TODO is this masking right? Especially for signed mul and div it's not so clear
                let bits = left.bits();
                let result = BitInt::from_unsigned(bits, result_full & BitInt::mask(bits)).unwrap();
                Const::new(ty, result)
            })
        }
        &InstructionInfo::Comparison { kind, left, right } => {
            eval_binary(map, left, right, |_, left, right| {
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
                Const::new(prog.ty_bool(), result)
            })
        }
        &InstructionInfo::Cast { ty, kind, value } => {
            // check that both are integer types, since that's the only thing cast supports for now
            let old_bits = prog.get_type(prog.type_of_value(value)).unwrap_int().unwrap();
            let new_bits = prog.get_type(ty).unwrap_int().unwrap();

            map.eval(value).map_known_const(|cst| {
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
        &InstructionInfo::BlackBox { .. } => Lattice::Overdef,
    };

    map.merge_value(prog, todo, instr.into(), result)
}

fn eval_binary(
    map: &mut LatticeMap,
    left: Value,
    right: Value,
    handle_const: impl Fn(Type, BitInt, BitInt) -> Const,
) -> Lattice {
    match (map.eval(left), map.eval(right)) {
        (Lattice::Undef, _) | (_, Lattice::Undef) => Lattice::Undef,

        (Lattice::Known(Value::Immediate(Immediate::Const(left))), Lattice::Known(Value::Immediate(Immediate::Const(right)))) => {
            assert_eq!(left.ty, right.ty);
            assert_eq!(left.value.bits(), right.value.bits());
            let ty = left.ty;

            let result = handle_const(ty, left.value, right.value);
            Lattice::Known(result.into())
        }

        //TODO sometimes this can be inferred as well, eg "0 * x" or "x == x"
        _ => Lattice::Overdef,
    }
}

fn apply_lattice_simplifications(prog: &mut Program, use_info: &UseInfo, lattice_map: &LatticeMap) -> usize {
    let mut count = 0;

    for (&value, &lattice_value) in &lattice_map.values {
        assert!(value_can_be_tracked(value));
        if let Lattice::Known(cst) = lattice_value {
            assert!(value_allowed_as_known(cst));
        }

        let ty = prog.type_of_value(value);
        if let Some(lattice_value) = lattice_value.as_value_of_type(prog, ty) {
            count += use_info.replace_value_usages(prog, value, lattice_value)
        }
    }

    count
}
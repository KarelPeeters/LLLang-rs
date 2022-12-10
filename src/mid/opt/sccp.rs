use std::collections::{HashSet, VecDeque};

use indexmap::map::IndexMap;

use crate::mid::analyse::use_info::{for_each_usage_in_instr, InstructionPos, Usage, UseInfo};
use crate::mid::ir::{ArithmeticOp, Block, Const, Function, Instruction, InstructionInfo, LogicalOp, Program, Target, Terminator, Value};
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

impl LatticeMap {
    fn eval(&self, value: Value) -> Lattice {
        match value {
            Value::Undef(_) =>
                Lattice::Undef,
            Value::Const(_) | Value::Func(_) | Value::Extern(_) | Value::Data(_) =>
                Lattice::Known(value),
            Value::Param(_) | Value::Phi(_) | Value::Instr(_) =>
                *self.values.get(&value).unwrap_or(&Lattice::Undef),
            Value::Slot(_) => Lattice::Overdef,
        }
    }

    fn merge_value(&mut self, todo: &mut VecDeque<Todo>, value: Value, new: Lattice) {
        assert!(matches!(value, Value::Param(_) | Value::Phi(_) | Value::Instr(_)));

        let prev = self.eval(value);
        let next = Lattice::merge(prev, new);
        self.values.insert(value, next);

        if prev != next {
            todo.push_back(Todo::ValueUsers(value));
        }
    }

    fn eval_func_return(&self, func: Function) -> Lattice {
        *self.func_returns.get(&func).unwrap_or(&Lattice::Undef)
    }

    fn merge_func_return(&mut self, todo: &mut VecDeque<Todo>, func: Function, lattice: Lattice) {
        let prev = self.eval_func_return(func);
        let next = Lattice::merge(prev, lattice);
        self.func_returns.insert(func, next);

        if prev != next {
            todo.push_back(Todo::FuncReturnUsers(func));
        }
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
                    todo.push_back(Todo::BlockInit(func, prog.get_func(func).entry.block))
                }
            }
            Todo::BlockInit(func, block) => {
                if blocks_reachable.insert(block) {
                    let block_info = prog.get_block(block);

                    //visit each instr
                    for &instr in &block_info.instructions {
                        visit_instr(&prog, &mut map, &mut todo, instr);
                        let pos = InstructionPos { func, block, instr };

                        //since it's the first time we check for usage of functions as generic operands
                        for_each_usage_in_instr(pos, prog.get_instr(instr), |value, usage| {
                            if let Value::Func(func) = value {
                                if !matches!(usage, Usage::CallTarget {..}) {
                                    // mark function parameters as overdefined
                                    for &param in &prog.get_func(func).params {
                                        map.values.insert(Value::Param(param), Lattice::Overdef);
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
                for &usage in &use_info[value] {
                    match usage {
                        Usage::Main | Usage::CallTarget { .. } =>
                            unreachable!("this value should never change: {:?}", usage),

                        //don't need to visit because their lattice value doesn't get affected by this operand
                        Usage::LoadAddr { .. } | Usage::StoreAddr { .. } => {}
                        Usage::TupleFieldPtrBase { .. } => {}
                        Usage::ArrayIndexPtrBase { .. } | Usage::ArrayIndexPtrIndex { .. } => {}

                        //don't need to visit because result is void
                        Usage::StoreValue { .. } => {}

                        Usage::BinaryOperandLeft { pos } | Usage::BinaryOperandRight { pos } => {
                            visit_instr(prog, &mut map, &mut todo, pos.instr);
                        }
                        Usage::TargetPhiValue { target_kind, phi_index } => {
                            let target = target_kind.get_target(prog);

                            let phi = prog.get_block(target.block).phis[phi_index];
                            let new_value = map.eval(target.phi_values[phi_index]);

                            map.merge_value(&mut todo, Value::Phi(phi), new_value)
                        }
                        Usage::CallArgument { pos, index } => {
                            match prog.get_instr(pos.instr) {
                                InstructionInfo::Call { target, args } => {
                                    if let &Value::Func(target) = target {
                                        //merge in argument
                                        let param = prog.get_func(target).params[index];
                                        map.merge_value(&mut todo, Value::Param(param), map.eval(args[index]));
                                    } else {
                                        //nothing to do here
                                    }
                                }
                                _ => unreachable!()
                            }
                        }
                        Usage::BranchCond { pos } => {
                            match &prog.get_block(pos.block).terminator {
                                Terminator::Branch { cond, true_target, false_target } => {
                                    visit_branch(prog, &mut map, &mut todo, pos.func, cond, true_target, false_target)
                                }
                                _ => unreachable!()
                            }
                        }
                        Usage::ReturnValue { pos } => {
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
            Todo::FuncReturnUsers(func) => {
                let return_lattice = map.eval_func_return(func);

                for &usage in &use_info[func] {
                    if let Usage::CallTarget { pos } = usage {
                        map.merge_value(&mut todo, Value::Instr(pos.instr), return_lattice);
                        todo.push_back(Todo::ValueUsers(Value::Instr(pos.instr)))
                    }
                }
            }
        }
    }

    map
}

fn visit_branch(
    prog: &Program,
    mut map: &mut LatticeMap,
    mut todo: &mut VecDeque<Todo>,
    func: Function,
    cond: &Value,
    true_target: &Target,
    false_target: &Target,
) {
    let cond = map.eval(*cond);
    let (visit_true, visit_false) = evaluate_branch_condition(prog, cond);

    if visit_true {
        update_target_reachable(prog, &mut map, &mut todo, func, true_target);
    }
    if visit_false {
        update_target_reachable(prog, &mut map, &mut todo, func, false_target);
    }
}

///Returns a tuple `(true_reachable, false_reachable)` for a branch on the given condition
fn evaluate_branch_condition(prog: &Program, cond: Lattice) -> (bool, bool) {
    match cond {
        Lattice::Undef => {
            //undefined behaviour, don't mark anything
            (false, false)
        }
        Lattice::Known(cst) => {
            if let Value::Const(cst) = cst {
                //if this is an actual boolean const we can fully evaluate it
                assert_eq!(prog.ty_bool(), cst.ty);
                let cst = cst.value != 0;
                (cst, !cst)
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
        map.merge_value(todo, Value::Phi(phi), map.eval(phi_value));
    }
}

fn visit_instr(prog: &Program, map: &mut LatticeMap, todo: &mut VecDeque<Todo>, instr: Instruction) {
    let instr_info = prog.get_instr(instr);

    let result = match instr_info {
        InstructionInfo::Load { .. } => Lattice::Overdef,
        InstructionInfo::TupleFieldPtr { .. } => Lattice::Overdef,
        InstructionInfo::PointerOffSet { .. } => Lattice::Overdef,
        InstructionInfo::Store { .. } => Lattice::Undef,
        InstructionInfo::Call { target, args } => {
            if let Value::Func(target) = *target {
                //mark reachable
                todo.push_back(Todo::FunctionInit(target));

                //merge in arguments
                let target_info = prog.get_func(target);
                for (&param, &arg) in zip_eq(&target_info.params, args) {
                    map.merge_value(todo, Value::Param(param), map.eval(arg))
                }

                //get return
                map.eval_func_return(target)
            } else {
                Lattice::Overdef
            }
        }
        &InstructionInfo::Arithmetic { kind, left, right } => {
            if let (
                Lattice::Known(Value::Const(left)),
                Lattice::Known(Value::Const(right))
            ) = (map.eval(left), map.eval(right)) {
                //TODO this probably doesn't handle wrapping correctly yet
                assert_eq!(left.ty, right.ty);
                let ty = left.ty;
                let (left, right) = (left.value, right.value);

                let result = match kind {
                    ArithmeticOp::Add => left + right,
                    ArithmeticOp::Sub => left - right,
                    ArithmeticOp::Mul => left * right,
                    //TODO are x/0 and x%0 undefined?
                    ArithmeticOp::Div => left / right,
                    ArithmeticOp::Mod => left % right,
                };

                Lattice::Known(Value::Const(Const { ty, value: result }))
            } else {
                //TODO sometimes this can be inferred as well, eg "0 * x"
                Lattice::Overdef
            }
        }
        &InstructionInfo::Comparison { kind, left, right } => {
            if let (
                Lattice::Known(Value::Const(left)),
                Lattice::Known(Value::Const(right))
            ) = (map.eval(left), map.eval(right)) {
                //TODO this probably doesn't handle wrapping correctly yet
                assert_eq!(left.ty, right.ty);
                let (left, right) = (left.value, right.value);

                let result = match kind {
                    LogicalOp::Eq => left == right,
                    LogicalOp::Neq => left != right,
                    LogicalOp::Gte => left >= right,
                    LogicalOp::Gt => left > right,
                    LogicalOp::Lte => left <= right,
                    LogicalOp::Lt => left < right,
                };

                Lattice::Known(Value::Const(Const { ty: prog.ty_bool(), value: result as i32 }))
            } else {
                //TODO sometimes this can be inferred as well, eg "0 & x"
                Lattice::Overdef
            }
        }
    };

    map.merge_value(todo, Value::Instr(instr), result)
}

fn apply_lattice_simplifications(prog: &mut Program, use_info: &UseInfo, lattice_map: &LatticeMap) -> usize {
    let mut count = 0;

    for (&value, &lattice_value) in &lattice_map.values {
        assert!(matches!(value, Value::Phi(_) | Value::Instr(_) | Value::Param(_)));
        if let Lattice::Known(cst) = lattice_value {
            assert!(cst.is_const_like());
        }

        let ty = prog.type_of_value(value);
        if let Some(lattice_value) = lattice_value.as_value_of_type(ty) {
            count += use_info.replace_value_usages(prog, value, lattice_value)
        }
    }

    count
}
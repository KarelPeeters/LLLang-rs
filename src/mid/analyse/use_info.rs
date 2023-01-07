use std::collections::VecDeque;
use std::fmt::Debug;

use indexmap::IndexSet;
use indexmap::map::{Entry, IndexMap};

use crate::mid::analyse::usage::{BlockPos, BlockUsage, ExprOperand, for_each_usage_in_expr, for_each_usage_in_instr, for_each_usage_in_term, InstrOperand, InstructionPos, TermOperand, TermUsage, Usage};
use crate::mid::ir::{Block, Expression, ExpressionInfo, Function, Global, Instruction, InstructionInfo, Program, Scoped, Terminator, Value};

//TODO maybe write a specialized version that only cares about specific usages for certain passes?
// eg. slot_to_phi only cares about slots
//TODO try to unify some of this code with gc

#[derive(Debug)]
pub struct UseInfo {
    func_blocks: IndexMap<Function, IndexSet<Block>>,
    value_usages: IndexMap<Value, Vec<Usage>>,
    block_usages: IndexMap<Block, Vec<BlockUsage>>,
    expressions: IndexSet<Expression>,
}

// TODO use visitor here as well
impl UseInfo {
    pub fn new(prog: &Program) -> Self {
        build_use_info(prog)
    }

    pub fn replace_value_usages(&self, prog: &mut Program, old: Value, new: Value) -> usize {
        self.replace_value_usages_if(prog, old, new, |_| true)
    }

    pub fn replace_value_usages_if(&self, prog: &mut Program, old: Value, new: Value, mut filter: impl FnMut(&Usage) -> bool) -> usize {
        assert_ne!(old, new);
        let mut count = 0;
        for usage in &self[old] {
            if filter(&usage) {
                repl_usage(prog, usage, old, new);
                count += 1;
            }
        }
        count
    }

    pub fn replace_block_usages(&self, prog: &mut Program, old: Block, new: Block) -> usize {
        assert_ne!(old, new);
        let mut count = 0;
        for &usage in &self[old] {
            repl(usage.get_field(prog), old, new);
            count += 1;
        }
        count
    }

    pub fn only_used_as_call_target(&self, func: Function) -> bool {
        self[func].iter().all(|usage| {
            matches!(usage, Usage::InstrOperand { pos: _, usage: InstrOperand::CallTarget })
        })
    }

    pub fn funcs(&self) -> impl Iterator<Item=Function> + '_ {
        self.func_blocks.keys().copied()
    }

    pub fn func_blocks(&self, func: Function) -> &IndexSet<Block> {
        self.func_blocks.get(&func).unwrap()
    }

    pub fn values(&self) -> impl Iterator<Item=Value> + '_ {
        self.value_usages.keys().copied()
    }

    pub fn instructions(&self) -> impl Iterator<Item=Instruction> + '_ {
        self.values().filter_map(|value| {
            match value {
                Value::Scoped(Scoped::Instr(instr)) => Some(instr),
                _ => None,
            }
        })
    }

    pub fn blocks(&self) -> impl Iterator<Item=Block> + '_ {
        self.block_usages.keys().copied()
    }

    /// Whether `value` is used anywhere in `func`, including through expressions.
    /// Can be used to check whether a function can directly call itself.
    pub fn value_used_in_func(&self, prog: &Program, value: Value, func: Function) -> bool {
        self[value].iter().any(|usage| {
            match usage.as_dom_pos() {
                Ok(pos) => pos.function() == Some(func),
                Err(expr) => self.value_used_in_func(prog, expr.into(), func),
            }
        })
    }
}

impl<T: Into<Value>> std::ops::Index<T> for UseInfo {
    type Output = [Usage];

    fn index(&self, index: T) -> &Self::Output {
        let index = index.into();
        self.value_usages.get(&index).map_or(&[], |v| v)
    }
}

impl std::ops::Index<Block> for UseInfo {
    type Output = [BlockUsage];

    fn index(&self, index: Block) -> &Self::Output {
        self.block_usages.get(&index).map_or(&[], |v| v)
    }
}

struct State<'a> {
    prog: &'a Program,
    info: UseInfo,

    todo_funcs: VecDeque<Function>,
    todo_blocks: VecDeque<BlockPos>,
    todo_exprs: VecDeque<Expression>,
}

fn build_use_info(prog: &Program) -> UseInfo {
    let mut state = State::new(prog);

    for (name, &func) in &prog.root_functions {
        state.add_usage(func.into(), Usage::RootFunction(name.to_owned()));
        state.todo_funcs.push_back(func);
    }

    loop {
        if let Some(func) = state.todo_funcs.pop_front() {
            state.visit_func(func);
            continue;
        }
        if let Some(block) = state.todo_blocks.pop_front() {
            state.visit_block(block);
            continue;
        }
        if let Some(expr) = state.todo_exprs.pop_front() {
            state.visit_expr(expr);
            continue;
        }

        assert!(state.todo_funcs.is_empty() && state.todo_blocks.is_empty() && state.todo_exprs.is_empty());
        break;
    }

    state.info
}

impl<'a> State<'a> {
    pub fn new(prog: &'a Program) -> Self {
        let info = UseInfo {
            func_blocks: Default::default(),
            value_usages: Default::default(),
            block_usages: Default::default(),
            expressions: Default::default(),
        };

        Self {
            prog,
            info,
            todo_funcs: Default::default(),
            todo_blocks: Default::default(),
            todo_exprs: Default::default(),
        }
    }

    fn add_usage(&mut self, value: Value, usage: Usage) {
        //we don't care about identity-less values
        if let Value::Immediate(_) = value { return; }

        // add usage
        self.info.value_usages.entry(value).or_default().push(usage);

        // potentially add to relevant queue
        match value {
            Value::Global(Global::Func(func)) => self.todo_funcs.push_back(func),
            Value::Expr(expr) => self.todo_exprs.push_back(expr),
            Value::Immediate(_) | Value::Global(_) | Value::Scoped(_) => {}
        }
    }

    fn add_block_usage(&mut self, block: Block, usage: BlockUsage) {
        self.info.block_usages.entry(block).or_default().push(usage);
    }

    fn visit_func(&mut self, func: Function) {
        let prog = self.prog;

        match self.info.func_blocks.entry(func) {
            Entry::Occupied(_) => {
                // we've already visited this function
            }
            Entry::Vacant(entry) => {
                entry.insert(IndexSet::default());

                let func_info = prog.get_func(func);
                let block_pos = BlockPos { func, block: func_info.entry };

                self.todo_blocks.push_back(block_pos);
                self.add_block_usage(func_info.entry, BlockUsage::FuncEntry(func));
            }
        }
    }

    fn visit_block(&mut self, block_pos: BlockPos) {
        let prog = self.prog;
        let BlockPos { func, block } = block_pos;

        if self.info.func_blocks.get_mut(&func).unwrap().insert(block) {
            let block_info = prog.get_block(block);
            let block_pos = BlockPos { func, block };

            //instructions
            for (instr_index, &instr) in block_info.instructions.iter().enumerate() {
                let instr_info = prog.get_instr(instr);
                let instr_pos = InstructionPos { func, block, instr, instr_index };

                for_each_usage_in_instr(instr_info, |value, usage| {
                    self.add_usage(value, Usage::InstrOperand { pos: instr_pos, usage });
                });
            }

            //terminator
            for_each_usage_in_term(
                &block_info.terminator,
                |usage| match usage {
                    TermUsage::Value(value, usage) => {
                        self.add_usage(value, Usage::TermOperand { pos: block_pos, usage });
                    }
                    TermUsage::Block(succ, kind) => {
                        self.todo_blocks.push_back(BlockPos { func, block: succ });
                        self.add_block_usage(succ, BlockUsage::Target { pos: block_pos, kind });
                    }
                },
            );
        }
    }

    fn visit_expr(&mut self, expr: Expression) {
        if !self.info.expressions.insert(expr) {
            // we've already visited this expression
            return;
        }

        let prog = self.prog;
        let expr_info = prog.get_expr(expr);

        for_each_usage_in_expr(expr_info, |value, usage| {
            self.add_usage(value, Usage::ExprOperand { expr, usage });
        });
    }
}

fn repl_usage(prog: &mut Program, usage: &Usage, old: Value, new: Value) {
    macro_rules! repl_unwrap {
        ($item:expr, $($pattern:pat)|+ => $result: expr) => {
            {
                let field = unwrap_match!($item, $($pattern)|+ => $result);
                repl(field, old, new);
            }
        }
    }

    match *usage {
        Usage::RootFunction(ref name) => {
            if let Some(new) = new.as_func() {
                let old = unwrap_match!(old, Value::Global(Global::Func(old)) => old);
                repl(prog.root_functions.get_mut(name).unwrap(), old, new)
            } else {
                panic!("Replacing root function with non-function value not supported")
            }
        }
        Usage::InstrOperand { pos, usage } => {
            let instr = prog.get_instr_mut(pos.instr);
            match usage {
                InstrOperand::LoadAddr =>
                    repl_unwrap!(instr, InstructionInfo::Load { addr, .. } => addr),
                InstrOperand::StoreAddr =>
                    repl_unwrap!(instr, InstructionInfo::Store { addr, .. } => addr),
                InstrOperand::StoreValue =>
                    repl_unwrap!(instr, InstructionInfo::Store { value, .. } => value),
                InstrOperand::CallTarget =>
                    repl_unwrap!(instr, InstructionInfo::Call { target, .. } => target),
                InstrOperand::CallArgument(index) =>
                    repl_unwrap!(instr, InstructionInfo::Call { args, .. } => &mut args[index]),
                InstrOperand::BlackBoxValue =>
                    repl_unwrap!(instr, InstructionInfo::BlackBox { value, .. } => value),
            }
        }
        Usage::ExprOperand { expr, usage } => {
            let expr = prog.get_expr_mut(expr);
            match usage {
                ExprOperand::BinaryOperandLeft =>
                    repl_unwrap!(expr, ExpressionInfo::Arithmetic { left, .. } | ExpressionInfo::Comparison { left, .. } => left),
                ExprOperand::BinaryOperandRight =>
                    repl_unwrap!(expr, ExpressionInfo::Arithmetic { right, .. } | ExpressionInfo::Comparison { right, .. } => right),
                ExprOperand::TupleFieldPtrBase =>
                    repl_unwrap!(expr, ExpressionInfo::TupleFieldPtr { base, .. } => base),
                ExprOperand::PointerOffSetBase =>
                    repl_unwrap!(expr, ExpressionInfo::PointerOffSet { base, .. } => base),
                ExprOperand::PointerOffSetIndex =>
                    repl_unwrap!(expr, ExpressionInfo::PointerOffSet { index, .. } => index),
                ExprOperand::CastValue =>
                    repl_unwrap!(expr, ExpressionInfo::Cast { value, .. } => value),
            }
        }
        Usage::TermOperand { pos, usage } => {
            let term = &mut prog.get_block_mut(pos.block).terminator;
            match usage {
                TermOperand::BranchCond =>
                    repl_unwrap!(term, Terminator::Branch { cond, .. } => cond),
                TermOperand::ReturnValue =>
                    repl_unwrap!(term, Terminator::Return { value } => value),
                TermOperand::TargetArg { kind, index } =>
                    repl(&mut kind.get_target_mut(term).args[index], old, new),
            }
        }
    }
}

fn repl<T: Eq + Debug>(field: &mut T, old: T, new: T) {
    assert!(
        *field == old,
        "Tried to replace {:?} -> {:?}, but was already replaced by {:?}",
        old, new, field,
    );
    *field = new;
}
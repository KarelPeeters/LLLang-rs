use indexmap::IndexMap;

use itertools::Itertools;
use crate::mid::analyse::usage::TermUsage;

use crate::mid::ir::{Block, BlockInfo, Expression, ExpressionInfo, Function, FunctionInfo, Instruction, Parameter, ParameterInfo, Program, Scoped, StackSlot, StackSlotInfo, Value};
use crate::util::arena::Arena;
use crate::util::internal_iter::InternalIterator;

#[derive(Debug)]
pub struct Recursive;

impl Program {
    pub fn deep_clone_function(&mut self, func: Function) -> Result<FunctionInfo, Recursive> {
        let old_info = self.get_func(func);

        let old_slots = old_info.slots.clone();
        let old_blocks = self.reachable_blocks(self.get_func(func).entry).collect_vec();

        let mut new_slots = vec![];
        let map_slot: IndexMap<_, _> = old_slots.iter().map(|&old_slot| {
            let &StackSlotInfo { inner_ty, ref debug_name } = self.get_slot(old_slot);
            let new_slot = self.define_slot(StackSlotInfo { inner_ty, debug_name: debug_name.clone() });
            new_slots.push(new_slot);
            (old_slot, new_slot)
        }).collect();

        let mut map_param = IndexMap::new();
        let mut map_instr = IndexMap::new();

        let map_block: IndexMap<_, _> = old_blocks.iter().map(|&old_block| {
            let old_block_info = self.get_block(old_block);

            let old_params = old_block_info.params.clone();
            let old_instrs = old_block_info.instructions.clone();
            // we don't need to do anything extra for terminator, this is already a deep clone
            let new_terminator = old_block_info.terminator.clone();
            let debug_name = old_block_info.debug_name.clone();

            let new_params = old_params.iter().map(|&old_param| {
                let &ParameterInfo { ty } = self.get_param(old_param);
                let new_param = self.define_param(ParameterInfo { ty });
                assert!(map_param.insert(old_param, new_param.into()).is_none());
                new_param
            }).collect_vec();

            let new_instructions = old_instrs.iter().map(|&old_instr| {
                let old_instr_info = self.get_instr(old_instr);
                let new_instr_info = old_instr_info.clone();
                let new_instr = self.define_instr(new_instr_info);
                assert!(map_instr.insert(old_instr, new_instr).is_none());
                new_instr
            }).collect_vec();

            let new_block_info = BlockInfo {
                params: new_params,
                // we replace terminator and instruction args later
                instructions: new_instructions,
                terminator: new_terminator,
                debug_name,
            };
            let new_block = self.define_block(new_block_info);
            (old_block, new_block)
        }).collect();

        let map_block_map = map_block;
        let map_block = |block: Block| {
            map_block_map.get(&block).copied().unwrap()
        };

        let mut mapper = ValueMapper {
            func,
            recursive: false,
            map_slot: &map_slot,
            map_param: &map_param,
            map_instr: &map_instr,
            map_expr: Default::default(),
            prog_exprs: &mut self.nodes.exprs,
        };

        for &new_instr in map_instr.values() {
            let new_instr = &mut self.nodes.instrs[new_instr];
            new_instr.replace_values(|value| mapper.map_value(value));
        }
        for &new_block in map_block_map.values() {
            let new_term = &mut self.nodes.blocks[new_block].terminator;

            new_term.operands_mut().for_each(|operand| {
                match operand {
                    TermUsage::Value(value, _) => *value = mapper.map_value(*value),
                    TermUsage::BlockTarget(block, _) => *block = map_block(*block),
                    TermUsage::BlockAffineBody(block) => *block = map_block(*block),
                }
            });
        }

        if mapper.recursive {
            return Err(Recursive);
        }

        let old_info = self.get_func(func);
        let new_entry = map_block(old_info.entry);

        let debug_name = old_info.debug_name.clone();

        let new_info = FunctionInfo {
            ty: old_info.ty,
            func_ty: old_info.func_ty.clone(),
            debug_name,
            entry: new_entry,
            slots: new_slots,
        };
        Ok(new_info)
    }
}

struct ValueMapper<'a> {
    func: Function,
    recursive: bool,

    map_slot: &'a IndexMap<StackSlot, StackSlot>,
    map_param: &'a IndexMap<Parameter, Value>,
    map_instr: &'a IndexMap<Instruction, Instruction>,
    map_expr: IndexMap<Expression, Expression>,

    prog_exprs: &'a mut Arena<Expression, ExpressionInfo>,
}

impl ValueMapper<'_> {
    fn map_value(&mut self, value: Value) -> Value {
        if value == self.func.into() {
            self.recursive = true;
        }

        match value {
            Value::Immediate(_) | Value::Global(_) => value,
            Value::Scoped(Scoped::Param(param)) => self.map_param.get(&param).copied().unwrap(),
            Value::Scoped(Scoped::Slot(slot)) => self.map_slot.get(&slot).copied().unwrap().into(),
            Value::Scoped(Scoped::Instr(instr)) => self.map_instr.get(&instr).copied().unwrap().into(),
            Value::Expr(expr) => self.map_expr(expr).into(),
        }
    }

    // Expressions are more difficult to map than other values:
    // * this is the first time we see them
    // * they can use other expressions
    fn map_expr(&mut self, expr: Expression) -> Expression {
        if let Some(&new_expr) = self.map_expr.get(&expr) {
            return new_expr;
        }

        // immediately define the new expression to break potentially infinite recursion
        let mut expr_info = self.prog_exprs[expr].clone();
        let new_expr = self.prog_exprs.push(expr_info.clone());
        self.map_expr.insert(expr, new_expr);

        // update the operands
        expr_info.replace_values(|value| self.map_value(value));
        self.prog_exprs[new_expr] = expr_info;

        new_expr
    }
}
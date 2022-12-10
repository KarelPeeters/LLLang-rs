use std::collections::{HashSet, VecDeque};

use crate::mid::ir::{Block, Program, Value};

pub trait Visitor {
    fn visit_value(&mut self, state: &mut VisitState, value: Value);

    fn visit_block(&mut self, state: &mut VisitState, block: Block);
}

pub struct VisitState<'a> {
    pub prog: &'a Program,

    visited_blocks: HashSet<Block>,
    visited_values: HashSet<Value>,

    todo_blocks: VecDeque<Block>,
    todo_values: VecDeque<Value>,
}

pub struct VisitedResult {
    pub visited_blocks: HashSet<Block>,
    pub visited_values: HashSet<Value>,
}

impl<'a> VisitState<'a> {
    pub fn new(prog: &'a Program) -> Self {
        Self {
            prog,
            visited_blocks: Default::default(),
            visited_values: Default::default(),
            todo_blocks: Default::default(),
            todo_values: Default::default(),
        }
    }

    pub fn add_value(&mut self, value: impl Into<Value>) {
        let value = value.into();

        match value {
            Value::Const(_) => {
                // we don't track const values
            }
            Value::Undef(_) | Value::Func(_) | Value::Param(_) | Value::Slot(_) |
            Value::Phi(_) | Value::Instr(_) | Value::Extern(_) | Value::Data(_) => {
                // track everything else
                if self.visited_values.insert(value) {
                    self.todo_values.push_back(value);
                }
            }
        }
    }

    pub fn add_block(&mut self, block: Block) {
        if self.visited_blocks.insert(block) {
            self.todo_blocks.push_back(block)
        }
    }

    pub fn run(mut self, mut visitor: impl Visitor) -> VisitedResult {
        while !self.todo_blocks.is_empty() || !self.todo_values.is_empty() {
            if let Some(block) = self.todo_blocks.pop_front() {
                visitor.visit_block(&mut self, block);
                continue;
            }

            if let Some(value) = self.todo_values.pop_front() {
                visitor.visit_value(&mut self, value);
                continue;
            }
        }

        assert!(self.todo_blocks.is_empty());
        assert!(self.todo_values.is_empty());

        VisitedResult {
            visited_blocks: self.visited_blocks,
            visited_values: self.visited_values,
        }
    }
}
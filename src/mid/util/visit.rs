use std::collections::{HashSet, VecDeque};

use crate::mid::ir::{Block, Program, Value};

pub trait Visitor {
    fn visit_value(&mut self, state: &mut VisitState, value: Value);

    fn visit_block(&mut self, state: &mut VisitState, block: Block);
}

pub struct VisitState<'p> {
    pub prog: &'p Program,

    visited_blocks: HashSet<Block>,
    visited_values: HashSet<Value>,

    todo_blocks: VecDeque<Block>,
    todo_values: VecDeque<Value>,
}

pub struct VisitedResult {
    pub visited_blocks: HashSet<Block>,
    pub visited_values: HashSet<Value>,
}

impl<'p> VisitState<'p> {
    pub fn new(prog: &'p Program) -> Self {
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
            Value::Immediate(_) => {
                // we don't track identity-less values
            }
            Value::Global(_) | Value::Scoped(_) | Value::Expr(_) => {
                // track everything else
                if self.visited_values.insert(value) {
                    self.todo_values.push_back(value);
                }
            }
        }
    }

    pub fn add_values<I: Into<Value>>(&mut self, values: impl IntoIterator<Item=I>) {
        for value in values.into_iter() {
            self.add_value(value.into());
        }
    }

    pub fn add_block(&mut self, block: Block) {
        if self.visited_blocks.insert(block) {
            self.todo_blocks.push_back(block)
        }
    }

    pub fn run(mut self, visitor: &mut impl Visitor) -> VisitedResult {
        loop {
            if let Some(block) = self.todo_blocks.pop_front() {
                visitor.visit_block(&mut self, block);
                continue;
            }

            if let Some(value) = self.todo_values.pop_front() {
                visitor.visit_value(&mut self, value);
                continue;
            }

            assert!(self.todo_blocks.is_empty());
            assert!(self.todo_values.is_empty());
            break;
        }

        VisitedResult {
            visited_blocks: self.visited_blocks,
            visited_values: self.visited_values,
        }
    }

    pub fn has_visited_value(&self, value: Value) -> bool {
        self.visited_values.contains(&value)
    }

    pub fn has_visited_block(&self, block: Block) -> bool {
        self.visited_blocks.contains(&block)
    }
}
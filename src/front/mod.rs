use std::fmt::{Debug, Formatter};

use crate::front::parser::{Token, TokenType};

pub mod ast;

pub mod parser;
pub mod resolve;

#[derive(Copy, Clone)]
pub struct Pos {
    line: usize,
    col: usize,
}

impl Debug for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}:{}", self.line, self.col))
    }
}

#[derive(Copy, Clone)]
pub struct Span {
    //inclusive
    pub start: Pos,
    //exclusive
    pub end: Pos,
}

impl Debug for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?} .. {:?}", self.start, self.end))
    }
}

impl Span {
    fn new(start: Pos, end: Pos) -> Self {
        Self { start, end }
    }

    fn empty(at: Pos) -> Self {
        Self::new(at, at)
    }
}

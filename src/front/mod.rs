use std::fmt::{Debug, Formatter};

pub mod ast;

pub mod parser;
pub mod lower;

#[derive(Copy, Clone)]
pub struct FileId {
    pub id: usize,
}

#[derive(Copy, Clone)]
pub struct Pos {
    file: FileId,
    line: usize,
    col: usize,
}

impl Debug for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        //TODO remove this convenience once there are proper error messages
        if self.file.id == 0 {
            f.write_fmt(format_args!("{}:{}", self.line, self.col))
        } else {
            f.write_fmt(format_args!("[{}]{}:{}", self.file.id, self.line, self.col))
        }
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

    fn empty_at(at: Pos) -> Self {
        Self::new(at, at)
    }
}

use std::fmt::{Debug, Formatter};

#[derive(Copy, Clone)]
pub struct FileId(pub usize);

impl Debug for FileId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("[{}]", self.0))
    }
}

#[derive(Copy, Clone)]
pub struct Pos {
    pub file: FileId,
    pub line: usize,
    pub col: usize,
}

impl Debug for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}{}:{}", self.file, self.line, self.col))
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
    pub fn new(start: Pos, end: Pos) -> Self {
        Self { start, end }
    }

    pub fn empty_at(at: Pos) -> Self {
        Self::new(at, at)
    }
}
#[derive(Debug)]
pub struct Function {
    pub entry: BasicBlock,
}

#[derive(Debug)]
pub struct BasicBlock {
    pub terminator: Terminator,
}

#[derive(Debug)]
pub enum Terminator {
    Return { value: i32 }
}

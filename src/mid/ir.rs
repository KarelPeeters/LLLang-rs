#[derive(Clone, Copy, Debug)]
pub enum Type {
    Bool,
    Int,
}

#[derive(Debug)]
pub struct Function {
    pub ret_type: Type,
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

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Basic { ty: Type, value: i32 }
}

#[derive(Debug)]
pub struct TypeDecl {
    pub string: String,
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub ret_type: TypeDecl,
    pub body: Block,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Return { value: String }
}
#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub body: Block,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Return { value: i32 }
}

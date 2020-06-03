use crate::front::Span;

#[derive(Debug)]
pub struct TypeDecl {
    pub span: Span,
    pub string: String,
}

#[derive(Debug)]
pub struct Function {
    pub span: Span,
    pub name: String,
    pub ret_type: TypeDecl,
    pub body: Block,
}

#[derive(Debug)]
pub struct Block {
    pub span: Span,
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    Return { value: Value }
}

#[derive(Debug)]
pub struct Value {
    pub span: Span,
    pub value: String,
}

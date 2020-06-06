use crate::front::Span;

#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub string: String,
}

#[derive(Debug)]
pub struct Function {
    pub span: Span,
    pub name: String,
    pub ret_type: Type,
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
    Declaration(Declaration),
    Expression(Box<Expression>),
}

#[derive(Debug)]
pub struct Declaration {
    pub span: Span,
    pub mutable: bool,
    pub name: String,
    pub ty: Option<Type>,
    pub init: Option<Box<Expression>>
}

#[derive(Debug)]
pub struct Expression {
    pub span: Span,
    pub kind: ExpressionKind,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Literal { value: String },
    Return { value: Box<Expression> },
}

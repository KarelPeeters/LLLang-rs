use crate::front::Span;

#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    Simple(String),
    Ref(Box<Type>),
}

#[derive(Debug)]
pub struct Identifier {
    pub span: Span,
    pub string: String,
}

#[derive(Debug)]
pub struct Function {
    pub span: Span,
    pub id: Identifier,
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
    Assignment(Assignment),
    Expression(Box<Expression>),
    If(IfStatement),
    Block(Block),
}

#[derive(Debug)]
pub struct Declaration {
    pub span: Span,
    pub mutable: bool,
    pub id: Identifier,
    pub ty: Option<Type>,
    pub init: Option<Box<Expression>>
}

#[derive(Debug)]
pub struct Assignment {
    pub span: Span,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

#[derive(Debug)]
pub struct IfStatement {
    pub span: Span,
    pub cond: Box<Expression>,
    pub then_block: Block,
    pub else_block: Option<Block>,
}

#[derive(Debug)]
pub struct Expression {
    pub span: Span,
    pub kind: ExpressionKind,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Literal { value: String },
    Identifier { id: Identifier },
    
    Ref { inner: Box<Expression> },
    DeRef { inner: Box<Expression> },

    Return { value: Box<Expression> },
}

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
    Func {
        params: Vec<Type>,
        ret: Box<Type>,
    }
}

#[derive(Debug)]
pub struct Identifier {
    pub span: Span,
    pub string: String,
}

#[derive(Debug)]
pub struct Program {
    pub items: Vec<Item>
}

#[derive(Debug)]
pub enum Item {
    Function(Function)
}

#[derive(Debug)]
pub struct Function {
    pub span: Span,
    pub ext: bool,
    pub id: Identifier,
    pub ret_ty: Option<Type>,
    pub params: Vec<Parameter>,
    pub body: Option<Block>,
}

#[derive(Debug)]
pub struct Parameter {
    pub span: Span,
    pub id: Identifier,
    pub ty: Type,
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
    While(WhileStatement),
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
pub struct WhileStatement {
    pub span: Span,
    pub cond: Box<Expression>,
    pub body: Block,
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

    Call {
        target: Box<Expression>,
        args: Vec<Expression>,
    },

    Binary {
        kind: BinaryOp,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Unary {
        kind: UnaryOp,
        inner: Box<Expression>,
    },

    Return { value: Option<Box<Expression>> },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnaryOp {
    Ref, Deref, Neg,
}

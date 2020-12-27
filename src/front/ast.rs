use indexmap::map::IndexMap;

use crate::front::pos::Span;

#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    Path(Path),
    Ref(Box<Type>),
    Func {
        params: Vec<Type>,
        ret: Box<Type>,
    },
    Tuple {
        fields: Vec<Type>
    },
}

#[derive(Debug)]
pub struct Identifier {
    pub span: Span,
    pub string: String,
}

#[derive(Debug)]
pub struct Path {
    pub span: Span,
    pub parents: Vec<Identifier>,
    pub id: Identifier,
}

//TODO remove
#[derive(Debug)]
pub struct Program {
    pub modules: IndexMap<String, Module>
}

#[derive(Debug)]
pub struct Module {
    pub items: Vec<Item>
}

#[derive(Debug)]
pub enum Item {
    UseDecl(UseDecl),
    Struct(Struct),
    Function(Function),
    Const(Declaration),
}

#[derive(Debug)]
pub struct UseDecl {
    pub span: Span,
    pub module: Identifier,
}

#[derive(Debug)]
pub struct Struct {
    pub span: Span,
    pub id: Identifier,
    pub fields: Vec<StructField>,
}

#[derive(Debug)]
pub struct StructField {
    pub span: Span,
    pub id: Identifier,
    pub ty: Type,
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
    For(ForStatement),
    Block(Block),
}

#[derive(Debug)]
pub struct Declaration {
    pub span: Span,
    pub mutable: bool,
    pub id: Identifier,
    pub ty: Option<Type>,
    pub init: Option<Box<Expression>>,
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
pub struct ForStatement {
    pub span: Span,
    pub index: Identifier,
    pub index_ty: Option<Type>,
    pub start: Box<Expression>,
    pub end: Box<Expression>,
    pub body: Block,
}

#[derive(Debug)]
pub struct Expression {
    pub span: Span,
    pub kind: ExpressionKind,
}

#[derive(Debug)]
pub enum ExpressionKind {
    IntLit { value: String },
    BoolLit { value: bool },
    StringLit { value: String },
    Null,

    Path(Path),

    Call {
        target: Box<Expression>,
        args: Vec<Expression>,
    },

    //TODO for now we're indexing by integer index but we actually want to index by string instead
    DotIndex {
        target: Box<Expression>,
        index: String,
    },

    Ternary {
        condition: Box<Expression>,
        then_value: Box<Expression>,
        else_value: Box<Expression>,
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
    Continue,
    Break,
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
    Gte,
    Gt,
    Lte,
    Lt,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnaryOp {
    Ref,
    Deref,
    Neg,
}

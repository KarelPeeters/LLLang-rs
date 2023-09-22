use crate::front::cst::IntTypeInfo;
use crate::front::pos::Span;
use crate::mid::ir::Signed;

#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    Wildcard,

    Void,
    Bool,
    Int(IntTypeInfo),
    IntSize(Signed),

    Path(Path),

    Ref(Box<Type>),
    Func {
        params: Vec<Type>,
        ret: Box<Type>,
    },
    Tuple {
        fields: Vec<Type>
    },
    Array {
        inner: Box<Type>,
        length: u32,
    },
}

#[derive(Debug)]
pub enum MaybeIdentifier {
    Identifier(Identifier),
    Placeholder(Span),
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

#[derive(Debug)]
pub struct ModuleContent {
    pub items: Vec<Item>,
}

#[derive(Debug)]
pub enum Item {
    UseDecl(UseDecl),
    TypeAlias(TypeAlias),
    Struct(Struct),
    Function(Function),
    ConstOrStatic(ConstOrStatic),
}

#[derive(Debug)]
pub struct ConstOrStatic {
    pub span: Span,
    pub kind: ConstOrStaticKind,
    pub id: Identifier,
    pub ty: Type,
    pub init: Expression,
}

#[derive(Debug, Copy, Clone)]
pub enum ConstOrStaticKind {
    Const,
    Static,
}

#[derive(Debug)]
pub struct UseDecl {
    pub span: Span,
    pub path: Path,
}

#[derive(Debug)]
pub struct TypeAlias {
    pub span: Span,
    pub id: Identifier,
    pub ty: Type,
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
    pub id: MaybeIdentifier,
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
    BinaryAssignment(BinaryAssignment),
    Expression(Box<Expression>),
    If(IfStatement),
    Loop(LoopStatement),
    While(WhileStatement),
    For(ForStatement),
    Block(Block),
}

#[derive(Debug)]
pub struct Declaration {
    pub span: Span,
    pub mutable: bool,
    pub id: MaybeIdentifier,
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
pub struct BinaryAssignment {
    pub span: Span,
    pub op: BinaryOp,
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
pub struct LoopStatement {
    pub span: Span,
    pub body: Block,
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
    pub index: MaybeIdentifier,
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
    Wrapped { inner: Box<Expression> },

    Null,
    BoolLit { value: bool },
    IntLit { value: String, ty: Option<Type> },
    StringLit { value: String },

    Path(Path),

    Call {
        target: Box<Expression>,
        args: Vec<Expression>,
    },

    // TODO think about a general way to represent intrinsics
    // TODO replace this with a generic lib function that then calls the intrinsic
    Obscure {
        value: Box<Expression>,
    },
    BlackHole {
        value: Box<Expression>,
    },
    MemBarrier,
    Unreachable,

    ArrayIndex {
        target: Box<Expression>,
        index: Box<Expression>,
    },
    DotIndex {
        target: Box<Expression>,
        index: DotIndexIndex,
    },

    Cast {
        value: Box<Expression>,
        ty: Type,
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
    Logical {
        kind: LogicalOp,
        left: Box<Expression>,
        right: Box<Expression>,
    },

    Return { value: Option<Box<Expression>> },
    Continue,
    Break,

    StructLiteral {
        struct_path: Path,
        fields: Vec<(Identifier, Expression)>,
    },
    ArrayLiteral {
        values: Vec<Expression>,
    },
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

    And,
    Or,
    Xor,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnaryOp {
    Ref,
    Deref,
    Neg,
    Not,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum LogicalOp {
    And,
    Or,
}

#[derive(Debug)]
pub enum DotIndexIndex {
    Tuple { span: Span, index: u32 },
    Struct(Identifier),
}
use crate::front::ast;
use crate::front::pos::Span;

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;
type TypeString = String;

#[derive(Debug)]
pub enum Error<'a> {
    //types
    InvalidType(&'a ast::Type),
    CannotInferType(Span),
    TypeMismatch {
        expression: &'a ast::Expression,
        expected: TypeString,
        actual: TypeString,
    },
    ExpectIntegerType {
        expression: &'a ast::Expression,
        actual: TypeString,
    },
    ExpectPointerType {
        expression: &'a ast::Expression,
        actual: TypeString,
    },
    ExpectFunctionType {
        expression: &'a ast::Expression,
        actual: TypeString,
    },
    ExpectStructOrTupleType {
        expression: &'a ast::Expression,
        actual: TypeString,
    },

    //dot indexing
    WrongDotIndexType {
        target: &'a ast::Expression,
        target_type: TypeString,
        index: &'a ast::DotIndexIndex,
    },
    StructFieldNotFound {
        target: &'a ast::Expression,
        target_type: TypeString,
        index: &'a ast::Identifier,
    },
    TupleIndexOutOfBounds {
        target: &'a ast::Expression,
        target_type: TypeString,
        index: u32,
    },

    //literals
    InvalidLiteralType {
        span: Span,
        ty: TypeString,
    },
    InvalidLiteral {
        span: Span,
        lit: String,
        ty: TypeString,
    },

    //lrvalue
    StoreIntoRValue(&'a ast::Expression),
    ReferenceOfLValue(&'a ast::Expression),

    //identifier
    UndeclaredIdentifier(&'a ast::Identifier),
    IdentifierDeclaredTwice(&'a ast::Identifier),

    //main
    NoMainModule,
    NoMainFunction,
    MainWrongItem,
    MainFunctionWrongType {
        expected: TypeString,
        actual: TypeString,
    },

    //functions
    MissingReturn(&'a ast::Identifier),
    MissingFunctionBody(&'a ast::Function),
    WrongArgCount {
        call: &'a ast::Expression,
        expected: usize,
        actual: usize,
    },

    //other
    NotInLoop {
        expr: &'a ast::Expression,
    },

    UnexpectedItemType {
        expected: ItemType,
        actual: ItemType,
        path: &'a ast::Path,
    },
}


#[derive(Debug, Eq, PartialEq)]
pub enum ItemType {
    Module,
    Type,
    Value,
}
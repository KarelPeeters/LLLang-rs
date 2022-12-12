use crate::front::ast;
use crate::front::pos::Span;

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;
type TypeString = String;

#[derive(Debug)]
pub enum Error<'a> {
    //types
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

    //literals
    ExpectedLiteral(&'a ast::Expression),
    InvalidLiteral {
        span: Span,
        lit: String,
        ty: TypeString,
    },
    StructLiteralForNonStructType {
        span: Span,
        ty: TypeString,
        fields: Vec<&'a ast::Identifier>,
    },
    StructLiteralInvalidFields {
        span: Span,
        expected: Vec<String>,
        actual: Vec<String>,
    },

    //lrvalue
    ExpectedLValue(&'a ast::Expression),
    ReferenceOfRValue(&'a ast::Expression),

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
    MainFunctionMustHaveBody,

    //functions
    MissingReturn(&'a ast::Identifier),
    MissingFunctionBody(&'a ast::Function),

    //other
    NotInLoop {
        expr: &'a ast::Expression,
    },
    UnexpectedItemType {
        expected: ItemType,
        actual: ItemType,
        path: &'a ast::Path,
    },
    DuplicateStructFields(&'a ast::Identifier),
}


#[derive(Debug, Eq, PartialEq)]
pub enum ItemType {
    Module,
    Type,
    Value,
}
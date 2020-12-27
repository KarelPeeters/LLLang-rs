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
    ExpectTypeGotItem {
        path: &'a ast::Path,
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
    StoreIntoRValue(Span),
    ReferenceOfLValue(Span),

    //identifier
    UndeclaredIdentifier(&'a ast::Identifier),
    IdentifierDeclaredTwice(&'a ast::Identifier),

    //main
    NoMainFunction,
    MainFunctionWrongType {
        expected: TypeString,
        actual: TypeString,
    },

    //functions
    MissingReturn(&'a ast::Function),
    MissingFunctionBody(&'a ast::Function),
    WrongArgCount {
        call: &'a ast::Expression,
        expected: usize,
        actual: usize,
    },

    //modules
    ModuleNotFound {
        module: &'a ast::Identifier,
    },
    ModuleNotUsed {
        module: &'a ast::Identifier,
    },

    //other
    NotInLoop {
        expr: &'a ast::Expression,
    },
}
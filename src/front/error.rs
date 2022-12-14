use std::num::ParseIntError;

use derive_more::From;

use crate::front::ast;
use crate::front::pos::Span;
use crate::mid::util::bit_int::BitOverflow;

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
    InvalidCastTypes {
        expression: &'a ast::Expression,
        ty_before: TypeString,
        ty_after: TypeString,
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
        reason: InvalidLiteralReason,
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ItemType {
    Module,
    Type,
    Value,
}

#[derive(Debug, Clone, Eq, PartialEq, From)]
pub enum InvalidLiteralReason {
    Parse(ParseIntError),
    BitOverFlow(BitOverflow),
}
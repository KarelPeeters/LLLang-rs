use std::num::ParseIntError;

use derive_more::From;

use crate::front::ast;
use crate::mid::util::bit_int::BitOverflow;

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;
type TypeString = String;

#[derive(Debug)]
pub enum Error<'a> {
    //types
    TypeMismatch {
        expected: TypeString,
        actual: TypeString,
        expression: &'a ast::Expression,
    },
    ExpectIntegerType {
        actual: TypeString,
        expression: &'a ast::Expression,
    },
    ExpectPointerType {
        actual: TypeString,
        expression: &'a ast::Expression,
    },
    ExpectStructOrTupleType {
        actual: TypeString,
        expression: &'a ast::Expression,
    },
    InvalidCastTypes {
        ty_before: TypeString,
        ty_after: TypeString,
        expression: &'a ast::Expression,
    },

    //dot indexing
    WrongDotIndexType {
        target_type: TypeString,
        index: &'a ast::DotIndexIndex,
        target: &'a ast::Expression,
    },
    StructFieldNotFound {
        target_type: TypeString,
        index: &'a ast::Identifier,
        target: &'a ast::Expression,
    },

    //literals
    ExpectedLiteral(&'a ast::Expression),
    InvalidLiteral {
        lit: String,
        ty: TypeString,
        reason: InvalidLiteralReason,
        expr: &'a ast::Expression,
    },
    StructLiteralForNonStructType {
        ty: TypeString,
        fields: Vec<&'a ast::Identifier>,
        expr: &'a ast::Expression,
    },
    StructLiteralInvalidFields {
        expected: Vec<String>,
        actual: Vec<String>,
        expr: &'a ast::Expression,
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
    DuplicateMainFunction,
    MainWrongItem,
    MainFunctionWrongType {
        expected: TypeString,
        actual: TypeString,
        func: &'a ast::Function,
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
    DuplicateExternSymbol(&'a ast::Identifier),
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
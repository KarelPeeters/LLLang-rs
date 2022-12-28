use std::mem::swap;
use std::num::ParseIntError;

use TokenType as TT;

use crate::front::ast;
use crate::front::cst::IntTypeInfo;
use crate::front::pos::{FileId, Pos, Span};

type Result<T> = std::result::Result<T, ParseError>;

#[derive(Debug)]
pub enum ParseError {
    Char {
        pos: Pos,
        char: char,
    },
    Token {
        pos: Pos,
        ty: TT,
        description: &'static str,
        allowed: Vec<TokenType>,
    },
    IntLit {
        span: Span,
        value: String,
        error: ParseIntError,
    },
    Eof {
        after: Pos,
        expected: &'static str,
    },
    CannotChainOperator {
        span: Span,
    },
}

macro_rules! declare_tokens {
    ($($token:ident$(($string:literal))?,)*) => {
        #[derive(Eq, PartialEq, Copy, Clone, Debug)]
        pub enum TokenType {
            $($token,)*
        }

        const TRIVIAL_TOKEN_LIST: &[(&'static str, TokenType)] = &[
            $($(($string, TokenType::$token),)?)*
        ];
    };
}

declare_tokens![
    Id,
    IntLit,
    StringLit,

    Void("void"),
    Bool("bool"),

    U8("u8"),
    U16("u16"),
    U32("u32"),
    I8("i8"),
    I16("i16"),
    I32("i32"),

    True("true"),
    False("false"),
    Null("null"),

    Extern("extern"),
    Use("use"),
    Type("type"),
    Struct("struct"),
    Fn("fn"),
    Return("return"),
    Let("let"),
    Const("const"),
    Mut("mut"),
    If("if"),
    Else("else"),
    Loop("loop"),
    While("while"),
    For("for"),
    In("in"),
    As("as"),
    Break("break"),
    Continue("continue"),
    BlackBox("__blackbox"),

    Underscore("_"),
    Arrow("->"),
    DoubleDot(".."),

    NotEq("!="),
    DoubleEq("=="),
    GreaterEqual(">="),
    Greater(">"),
    LessEqual("<="),
    Less("<"),

    Plus("+"),
    Minus("-"),
    Slash("/"),
    Percent("%"),

    DoubleAmpersand("&&"),
    DoublePipe("||"),

    Dot("."),
    DoubleColon("::"),
    Semi(";"),
    Colon(":"),
    QuestionMark("?"),
    Comma(","),
    Eq("="),
    Ampersand("&"),
    Star("*"),
    Pipe("|"),
    Hat("^"),

    OpenB("("),
    CloseB(")"),
    OpenC("{"),
    CloseC("}"),
    OpenS("["),
    CloseS("]"),

    Eof,
];

#[derive(Debug)]
pub struct Token {
    ty: TT,
    string: String,
    span: Span,
}

impl Token {
    fn eof_token(pos: Pos) -> Token {
        Token {
            ty: TT::Eof,
            string: "".to_string(),
            span: Span::empty_at(pos),
        }
    }
}

struct Tokenizer<'s> {
    left: &'s str,
    pos: Pos,

    curr: Token,
    next: Token,
}

impl<'s> Tokenizer<'s> {
    fn new(file: FileId, left: &'s str) -> Result<Self> {
        let pos = Pos { file, line: 1, col: 1 };
        let mut result = Self {
            left,
            pos,
            curr: Token::eof_token(pos),
            next: Token::eof_token(pos),
        };
        result.advance()?;
        result.advance()?;
        Ok(result)
    }

    /// self.left should only be advanced trough this function to ensure self.pos is updated
    fn skip_count(&mut self, count: usize) -> &str {
        //update position
        let skipped = &self.left[0..count];
        if let Some(last_newline) = skipped.rfind('\n') {
            self.pos.col = count - last_newline;
            self.pos.line += skipped.matches('\n').count();
        } else {
            self.pos.col += count;
        }

        self.left = &self.left[count..];

        skipped
    }

    fn skip_past(&mut self, pattern: &'static str, allow_eof: bool) -> Result<()> {
        let start_pos = self.pos;

        match self.left.find(pattern) {
            Some(i) => {
                //skip up to and including the pattern
                self.skip_count(i + pattern.len());
                Ok(())
            }
            None => {
                if !allow_eof { return Err(ParseError::Eof { after: start_pos, expected: pattern }); }

                //skip to the end
                self.skip_count(self.left.len());
                Ok(())
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) -> Result<()> {
        loop {
            let prev_left = self.left;
            self.skip_count(self.left.len() - self.left.trim_start().len());

            if self.left.starts_with("//") {
                self.skip_past("\n", true)?;
            }
            if self.left.starts_with("/*") {
                self.skip_past("*/", false)?;
            }

            if prev_left == self.left { return Ok(()); }
        }
    }

    fn parse_int_lit(&mut self) -> Result<Option<Token>> {
        let mut offset = 0;
        let start_pos = self.pos;

        let minus = self.left[offset..].starts_with('-');
        if minus {
            offset += 1;
        }

        let hex = self.left[offset..].starts_with("0x");
        if minus && hex {
            // negative hex literals are not useful, there is no "most negative" edge case anyway
            // we cancel parsing an int here, we want "(-) (0x..)", not "(-0) (x..)" which we are currently trying
            return Ok(None);
        }

        let is_digit = if hex {
            offset += 2;
            char::is_ascii_hexdigit
        } else {
            char::is_ascii_digit
        };

        let peek = match self.left[offset..].chars().next() {
            None => {
                self.skip_count(offset);
                return Err(ParseError::Eof { after: self.pos, expected: "integer literal digits" });
            }
            Some(peek) => peek,
        };
        if !is_digit(&peek) {
            self.skip_count(offset);
            return Err(ParseError::Char { pos: self.pos, char: peek });
        }

        let digits = self.left[offset..].find(|c: char| !is_digit(&c)).unwrap_or(self.left[offset..].len());
        let string = self.skip_count(offset + digits).to_owned();

        Ok(Some(Token {
            ty: TT::IntLit,
            string,
            span: Span::new(start_pos, self.pos),
        }))
    }

    fn parse_next(&mut self) -> Result<Token> {
        self.skip_whitespace_and_comments()?;
        let start_pos = self.pos;

        let peek = if let Some(peek) = self.left.chars().next() {
            peek
        } else {
            return Ok(Token::eof_token(start_pos));
        };
        let lookahead = self.left.chars().nth(1);

        //integer literal
        if peek.is_ascii_digit() || (peek == '-' && lookahead.as_ref().map_or(false, char::is_ascii_digit)) {
            if let Some(token) = self.parse_int_lit()? {
                return Ok(token);
            }
        }

        //identifier
        if peek.is_alphabetic() || peek == '_' {
            let end = self.left
                .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '@'))
                .unwrap_or(self.left.len());
            let string = self.skip_count(end).to_owned();

            //check if it it happens to be a keyword:
            let ty = TRIVIAL_TOKEN_LIST.iter()
                .find(|(pattern, _)| pattern == &string)
                .map(|&(_, ty)| ty)
                .unwrap_or(TT::Id);

            return Ok(Token {
                ty,
                string,
                span: Span::new(start_pos, self.pos),
            });
        }

        //string literal
        if peek == '"' {
            let end = 1 + self.left[1..].find('"')
                .ok_or(ParseError::Eof { after: self.pos, expected: "\"" })?;
            let content = self.skip_count(end + 1)[1..end].to_owned();

            return Ok(Token {
                ty: TT::StringLit,
                string: content,
                span: Span::new(start_pos, self.pos),
            });
        }

        //trivial token
        for (pattern, ty) in TRIVIAL_TOKEN_LIST {
            if self.left.starts_with(pattern) {
                self.skip_count(pattern.len());
                let end_pos = self.pos;
                return Ok(Token {
                    ty: *ty,
                    string: pattern.to_string(),
                    span: Span::new(start_pos, end_pos),
                });
            }
        }

        Err(ParseError::Char {
            pos: self.pos,
            char: peek,
        })
    }

    fn advance(&mut self) -> Result<Token> {
        let next = self.parse_next()?;

        let mut result = Token::eof_token(self.pos);

        swap(&mut result, &mut self.curr);
        swap(&mut self.curr, &mut self.next);

        self.next = next;
        Ok(result)
    }
}

#[derive(Debug)]
struct Restrictions {
    no_struct_literal: bool,
    no_ternary: bool,
}

impl Restrictions {
    const NONE: Restrictions = Restrictions { no_struct_literal: false, no_ternary: false };
    const NO_STRUCT_LITERAL: Restrictions = Restrictions { no_struct_literal: true, no_ternary: false };
    const NO_TERNARY: Restrictions = Restrictions { no_struct_literal: false, no_ternary: true };
}

struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
    last_popped_end: Pos,
    restrictions: Restrictions,
}

const EXPR_START_TOKENS: &[TT] = &[
    TT::Return,
    TT::Ampersand,
    TT::Star,
    TT::Minus,
    TT::IntLit,
    TT::True,
    TT::False,
    TT::Id,
    TT::OpenB,
];

const TYPE_START_TOKENS: &[TT] = &[
    TT::Underscore,
    TT::Void,
    TT::Bool,
    TT::U8,
    TT::U16,
    TT::U32,
    TT::I8,
    TT::I16,
    TT::I32,
    TT::Ampersand,
    TT::Id,
    TT::OpenB,
    TT::OpenS
];

#[derive(Debug, Copy, Clone)]
enum ParseBinaryOp {
    Binary(ast::BinaryOp),
    Logical(ast::LogicalOp),
}

#[derive(Debug)]
struct BinOpInfo {
    level: u8,
    token: TT,
    allow_chain: bool,
    op: ParseBinaryOp,
}

const BINARY_OPERATOR_INFO: &[BinOpInfo] = &[
    // logical
    BinOpInfo { level: 1, token: TT::DoublePipe, allow_chain: true, op: ParseBinaryOp::Logical(ast::LogicalOp::Or) },
    BinOpInfo { level: 2, token: TT::DoubleAmpersand, allow_chain: true, op: ParseBinaryOp::Logical(ast::LogicalOp::And) },
    // comparison
    BinOpInfo { level: 3, token: TT::DoubleEq, allow_chain: false, op: ParseBinaryOp::Binary(ast::BinaryOp::Eq) },
    BinOpInfo { level: 3, token: TT::NotEq, allow_chain: false, op: ParseBinaryOp::Binary(ast::BinaryOp::Neq) },
    BinOpInfo { level: 3, token: TT::GreaterEqual, allow_chain: false, op: ParseBinaryOp::Binary(ast::BinaryOp::Gte) },
    BinOpInfo { level: 3, token: TT::Greater, allow_chain: false, op: ParseBinaryOp::Binary(ast::BinaryOp::Gt) },
    BinOpInfo { level: 3, token: TT::LessEqual, allow_chain: false, op: ParseBinaryOp::Binary(ast::BinaryOp::Lte) },
    BinOpInfo { level: 3, token: TT::Less, allow_chain: false, op: ParseBinaryOp::Binary(ast::BinaryOp::Lt) },
    // bitwise
    BinOpInfo { level: 4, token: TT::Pipe, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Or) },
    BinOpInfo { level: 5, token: TT::Hat, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Xor) },
    BinOpInfo { level: 6, token: TT::Ampersand, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::And) },
    // add/sub
    BinOpInfo { level: 7, token: TT::Plus, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Add) },
    BinOpInfo { level: 7, token: TT::Minus, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Sub) },
    // mul/div/mod
    BinOpInfo { level: 8, token: TT::Star, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Mul) },
    BinOpInfo { level: 8, token: TT::Slash, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Div) },
    BinOpInfo { level: 8, token: TT::Percent, allow_chain: true, op: ParseBinaryOp::Binary(ast::BinaryOp::Mod) },
];

struct PrefixOpInfo {
    level: u8,
    token: TT,
    op: ast::UnaryOp,
}

const PREFIX_OPERATOR_INFO: &[PrefixOpInfo] = &[
    PrefixOpInfo { level: 2, token: TT::Ampersand, op: ast::UnaryOp::Ref },
    PrefixOpInfo { level: 2, token: TT::Star, op: ast::UnaryOp::Deref },
    PrefixOpInfo { level: 2, token: TT::Minus, op: ast::UnaryOp::Neg },
];

const POSTFIX_DEFAULT_LEVEL: u8 = 3;
const POSTFIX_CAST_LEVEL: u8 = 1;

/// The data required to construct a prefix expression.
struct PrefixState {
    level: u8,
    start: Pos,
    op: ast::UnaryOp,
}

impl PrefixState {
    fn apply(self, inner: ast::Expression) -> ast::Expression {
        let inner = Box::new(inner);
        ast::Expression {
            span: Span::new(self.start, inner.span.end),
            kind: ast::ExpressionKind::Unary { kind: self.op, inner },
        }
    }
}

/// The data required to construct a postfix expression.
struct PostFixState {
    level: u8,
    end: Pos,
    kind: PostFixStateKind,
}

impl PostFixState {
    fn apply(self, inner: ast::Expression) -> ast::Expression {
        let inner = Box::new(inner);
        let span = Span::new(inner.span.start, self.end);

        let kind = match self.kind {
            PostFixStateKind::Call { args } =>
                ast::ExpressionKind::Call { target: inner, args },
            PostFixStateKind::ArrayIndex { index } =>
                ast::ExpressionKind::ArrayIndex { target: inner, index },
            PostFixStateKind::DotIndex { index } =>
                ast::ExpressionKind::DotIndex { target: inner, index },
            PostFixStateKind::Cast { ty } =>
                ast::ExpressionKind::Cast { value: inner, ty },
        };

        ast::Expression { span, kind }
    }
}

enum PostFixStateKind {
    Call { args: Vec<ast::Expression> },
    ArrayIndex { index: Box<ast::Expression> },
    DotIndex { index: ast::DotIndexIndex },
    Cast { ty: ast::Type },
}

#[allow(dead_code)]
impl<'s> Parser<'s> {
    fn pop(&mut self) -> Result<Token> {
        let token = self.tokenizer.advance()?;
        self.last_popped_end = token.span.end;
        Ok(token)
    }

    fn peek(&self) -> &Token {
        &self.tokenizer.curr
    }

    fn lookahead(&self) -> &Token {
        &self.tokenizer.next
    }

    fn at(&mut self, ty: TT) -> bool {
        self.peek().ty == ty
    }

    /// pop and return the next token if the type matches, otherwise do nothing and return None
    fn accept(&mut self, ty: TT) -> Result<Option<Token>> {
        if self.at(ty) {
            self.pop().map(Some)
        } else {
            Ok(None)
        }
    }

    /// pop and return the next token if the type matches, otherwise return an error
    fn expect(&mut self, ty: TT, description: &'static str) -> Result<Token> {
        if self.at(ty) {
            self.pop()
        } else {
            Err(Self::unexpected_token(
                self.peek(),
                &[ty],
                description,
            ))
        }
    }

    /// call `expect` on each type in sequence, return an error if any `expect` fails
    fn expect_all(&mut self, tys: &[TT], description: &'static str) -> Result<()> {
        for &ty in tys {
            self.expect(ty, description)?;
        }
        Ok(())
    }

    /// pop and return the next token if the type matches any of the given types, otherwise return an error
    fn expect_any(&mut self, tys: &'static [TT], description: &'static str) -> Result<Token> {
        if tys.contains(&self.peek().ty) {
            Ok(self.pop()?)
        } else {
            Err(Self::unexpected_token(self.peek(), tys, description))
        }
    }

    fn unexpected_token(token: &Token, allowed: &[TT], description: &'static str) -> ParseError {
        ParseError::Token {
            ty: token.ty,
            pos: token.span.start,
            allowed: allowed.iter().copied().collect(),
            description,
        }
    }

    fn list<A, F: FnMut(&mut Self) -> Result<A>>(
        &mut self,
        end: TT,
        sep: Option<TT>,
        mut item: F,
    ) -> Result<(Span, Vec<A>)> {
        let mut result = Vec::new();
        let start_pos = self.peek().span.start;
        let mut end_pos = start_pos;

        while self.accept(end)?.is_none() {
            result.push(item(self)?);
            end_pos = self.last_popped_end;

            if self.accept(end)?.is_some() { break; }

            if let Some(sep) = sep {
                self.expect(sep, "separator")?;
            }
        }

        Ok((Span::new(start_pos, end_pos), result))
    }
}

impl<'s> Parser<'s> {
    fn restrict<T>(&mut self, res: Restrictions, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = std::mem::replace(&mut self.restrictions, res);
        let result = f(self);
        self.restrictions = old;
        result
    }

    fn unrestrict<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.restrict(Restrictions::NONE, f)
    }

    fn module(&mut self) -> Result<ast::ModuleContent> {
        let (_, items) = self.list(TT::Eof, None, Self::item)?;
        Ok(ast::ModuleContent { items })
    }

    fn item(&mut self) -> Result<ast::Item> {
        let token = self.peek();

        match token.ty {
            TT::Struct => self.struct_().map(ast::Item::Struct),
            TT::Fn | TT::Extern => self.function().map(ast::Item::Function),
            TT::Const => self.const_().map(ast::Item::Const),
            TT::Use => self.use_decl().map(ast::Item::UseDecl),
            TT::Type => self.type_alias().map(ast::Item::TypeAlias),
            _ => Err(Self::unexpected_token(token, &[TT::Struct, TT::Fn, TT::Extern, TT::Const, TT::Use], "start of item"))
        }
    }

    fn const_(&mut self) -> Result<ast::Const> {
        let start_pos = self.expect(TT::Const, "start of const item")?.span.start;
        let id = self.identifier("const name")?;
        self.expect(TT::Colon, "const type")?;
        let ty = self.type_decl()?;
        self.expect(TT::Eq, "initializer")?;
        let init = self.expression()?;
        self.expect(TT::Semi, "end of item")?;

        let span = Span::new(start_pos, self.last_popped_end);
        Ok(ast::Const { span, id, ty, init })
    }

    fn use_decl(&mut self) -> Result<ast::UseDecl> {
        let start_pos = self.expect(TT::Use, "start of use decl")?.span.start;
        let path = self.path()?;
        self.expect(TT::Semi, "end of item")?;

        let span = Span::new(start_pos, path.span.end);
        Ok(ast::UseDecl { span, path })
    }

    fn type_alias(&mut self) -> Result<ast::TypeAlias> {
        let start_pos = self.expect(TT::Type, "start of type alias")?.span.start;
        let id = self.identifier("type alias name")?;
        self.expect(TT::Eq, "type alias equal sign")?;
        let ty = self.type_decl()?;
        self.expect(TT::Semi, "type alias end")?;

        let span = Span::new(start_pos, self.last_popped_end);
        Ok(ast::TypeAlias { span, id, ty })
    }

    fn struct_(&mut self) -> Result<ast::Struct> {
        let start = self.expect(TT::Struct, "start of struct declaration")?.span.start;
        let id = self.identifier("struct name")?;
        self.expect(TT::OpenC, "start of struct fields")?;

        let (_, fields) = self.list(TT::CloseC, Some(TT::Comma), Self::struct_field)?;

        let span = Span::new(start, self.last_popped_end);
        Ok(ast::Struct { span, id, fields })
    }

    fn struct_field(&mut self) -> Result<ast::StructField> {
        let id = self.identifier("field name")?;
        self.expect(TT::Colon, "field type")?;
        let ty = self.type_decl()?;

        let span = Span::new(id.span.start, ty.span.end);
        Ok(ast::StructField { span, id, ty })
    }

    fn function(&mut self) -> Result<ast::Function> {
        let start_pos = self.peek().span.start;

        let ext = self.accept(TT::Extern)?.is_some();
        self.expect(TT::Fn, "function declaration")?;
        let id = self.identifier("function name")?;

        self.expect(TT::OpenB, "start of parameters")?;
        let (_, params) = self.list(TT::CloseB, Some(TT::Comma), Self::parameter)?;

        let ret_ty = if self.accept(TT::Arrow)?.is_some() {
            Some(self.type_decl()?)
        } else {
            None
        };

        let body = if self.at(TT::OpenC) {
            Some(self.block()?)
        } else {
            self.expect(TT::Semi, "end of function declaration")?;
            None
        };

        let span = Span::new(start_pos, self.last_popped_end);
        Ok(ast::Function { span, ext, id, ret_ty, params, body })
    }

    fn parameter(&mut self) -> Result<ast::Parameter> {
        let start = self.peek().span.start;
        let id = self.maybe_identifier("parameter name")?;
        self.expect(TT::Colon, "parameter type")?;
        let ty = self.type_decl()?;

        let span = Span::new(start, ty.span.end);
        Ok(ast::Parameter { span, id, ty })
    }

    fn block(&mut self) -> Result<ast::Block> {
        let start_pos = self.expect(TT::OpenC, "start of block")?.span.start;
        let (span, statements) = self.list(TT::CloseC, None, Self::statement)?;

        Ok(ast::Block { span: Span::new(start_pos, span.end), statements })
    }

    fn statement(&mut self) -> Result<ast::Statement> {
        let token = self.peek();
        let start_pos = token.span.start;

        let (kind, need_semi) = match token.ty {
            TT::Let => {
                //declaration
                let decl = self.variable_declaration(TT::Let)?;
                (ast::StatementKind::Declaration(decl), true)
            }
            TT::If => {
                self.pop()?;
                let cond = self.restrict(Restrictions::NO_STRUCT_LITERAL, |s| s.expression_boxed())?;
                let then_block = self.block()?;

                let else_block = self.accept(TT::Else)?
                    .map(|_| self.block())
                    .transpose()?;

                (ast::StatementKind::If(ast::IfStatement {
                    span: Span::new(start_pos, self.last_popped_end),
                    cond,
                    then_block,
                    else_block,
                }), false)
            }
            TT::Loop => {
                self.pop()?;

                let body = self.block()?;
                let span = Span::new(start_pos, self.last_popped_end);
                (ast::StatementKind::Loop(ast::LoopStatement { span, body }), false)
            }
            TT::While => {
                self.pop()?;

                let cond = self.restrict(Restrictions::NO_STRUCT_LITERAL, |s| s.expression_boxed())?;
                let body = self.block()?;

                let span = Span::new(start_pos, self.last_popped_end);
                (ast::StatementKind::While(ast::WhileStatement { span, cond, body }), false)
            }
            TT::For => {
                self.pop()?;

                let index = self.maybe_identifier("index variable")?;
                let index_ty = self.maybe_type_decl()?;

                self.expect(TT::In, "in")?;
                let start = self.expression_boxed()?;
                self.expect(TT::DoubleDot, "range separator")?;

                let end = self.restrict(Restrictions::NO_STRUCT_LITERAL, |s| {
                    s.expression_boxed()
                })?;

                let body = self.block()?;

                let span = Span::new(start_pos, self.last_popped_end);
                (ast::StatementKind::For(ast::ForStatement { span, index, index_ty, start, end, body }), false)
            }
            TT::OpenC => {
                let block = self.unrestrict(|s| s.block())?;
                (ast::StatementKind::Block(block), false)
            }
            _ => {
                let left = self.expression_boxed()?;

                let kind = if self.accept(TT::Eq)?.is_some() {
                    //assignment
                    let right = self.expression_boxed()?;
                    ast::StatementKind::Assignment(ast::Assignment {
                        span: Span::new(left.span.start, right.span.end),
                        left,
                        right,
                    })
                } else {
                    //expression
                    ast::StatementKind::Expression(left)
                };

                (kind, true)
            }
        };

        if need_semi {
            self.expect(TT::Semi, "end of statement")?;
        }

        let span = Span::new(start_pos, self.last_popped_end);
        Ok(ast::Statement { span, kind })
    }

    fn variable_declaration(&mut self, ty: TT) -> Result<ast::Declaration> {
        let start_pos = self.expect(ty, "variable declaration")?.span.start;
        let mutable = self.accept(TT::Mut)?.is_some();
        let id = self.maybe_identifier("variable name")?;

        let ty = self.maybe_type_decl()?;
        let init = self.accept(TT::Eq)?
            .map(|_| self.expression_boxed())
            .transpose()?;

        Ok(ast::Declaration { span: Span::new(start_pos, self.last_popped_end), mutable, ty, id, init })
    }

    fn expression_boxed(&mut self) -> Result<Box<ast::Expression>> {
        Ok(Box::new(self.expression()?))
    }

    fn expression(&mut self) -> Result<ast::Expression> {
        let expr = self.precedence_climb_binop(0, true)?;
        let start = expr.span.start;

        if !self.restrictions.no_ternary && self.accept(TT::QuestionMark)?.is_some() {
            let then_value = self.expression()?;
            self.expect(TT::Colon, "continue ternary expression")?;
            let else_value = self.expression()?;

            let kind = ast::ExpressionKind::Ternary {
                condition: Box::new(expr),
                then_value: Box::new(then_value),
                else_value: Box::new(else_value),
            };

            Ok(ast::Expression {
                span: Span::new(start, self.last_popped_end),
                kind,
            })
        } else {
            Ok(expr)
        }
    }

    fn precedence_climb_binop(&mut self, level: u8, allow_chain: bool) -> Result<ast::Expression> {
        let mut curr = self.unary()?;

        loop {
            let token = self.peek();
            let info = BINARY_OPERATOR_INFO.iter()
                .find(|i| i.token == token.ty);

            if let Some(info) = info {
                if info.level == level && !allow_chain {
                    return Err(ParseError::CannotChainOperator { span: token.span });
                }
                if info.level <= level {
                    break;
                }

                self.pop()?;

                let right = self.precedence_climb_binop(info.level, info.allow_chain)?;

                let left = Box::new(curr);
                let right = Box::new(right);
                let span = Span::new(left.span.start, right.span.end);

                let kind = match info.op {
                    ParseBinaryOp::Binary(kind) => ast::ExpressionKind::Binary { kind, left, right },
                    ParseBinaryOp::Logical(kind) => ast::ExpressionKind::Logical { kind, left, right },
                };

                curr = ast::Expression { span, kind }
            } else {
                break;
            }
        }

        Ok(curr)
    }

    fn unary(&mut self) -> Result<ast::Expression> {
        //collect all operators
        let mut prefix_ops = self.collect_prefix_ops()?;
        let curr = self.atomic()?;
        let mut postfix_ops = self.collect_postfix_ops()?;

        //postfix operations should be applied first-to-last, so reverse
        postfix_ops.reverse();

        //apply operations last-to-first, choosing between pre- and postfix depending on their levels
        let mut curr = curr;
        loop {
            let prefix_level = prefix_ops.last().map(|s| s.level);
            let postfix_level = postfix_ops.last().map(|s| s.level);

            match (prefix_level, postfix_level) {
                (Some(prefix_level), Some(postfix_level)) => {
                    assert_ne!(prefix_level, postfix_level);
                    if prefix_level > postfix_level {
                        curr = prefix_ops.pop().unwrap().apply(curr);
                    } else {
                        curr = postfix_ops.pop().unwrap().apply(curr);
                    }
                }
                (Some(_), None) => {
                    curr = prefix_ops.pop().unwrap().apply(curr);
                }
                (None, Some(_)) => {
                    curr = postfix_ops.pop().unwrap().apply(curr);
                }
                (None, None) => break
            }
        }

        Ok(curr)
    }

    fn collect_prefix_ops(&mut self) -> Result<Vec<PrefixState>> {
        let mut result = Vec::new();

        loop {
            let token = self.peek();
            let info = PREFIX_OPERATOR_INFO.iter()
                .find(|i| i.token == token.ty);

            if let Some(info) = info {
                let token = self.pop()?;
                result.push(PrefixState { level: info.level, start: token.span.start, op: info.op });
            } else {
                break;
            }
        }

        Ok(result)
    }

    fn collect_postfix_ops(&mut self) -> Result<Vec<PostFixState>> {
        let mut result = Vec::new();

        loop {
            let token = self.peek();

            let (level, kind) = match token.ty {
                TT::OpenB => {
                    //call
                    self.pop()?;
                    let (_, args) = self.list(TT::CloseB, Some(TT::Comma), Self::expression)?;

                    (POSTFIX_DEFAULT_LEVEL, PostFixStateKind::Call { args })
                }
                TT::OpenS => {
                    //array indexing
                    self.pop()?;
                    let index = self.expression_boxed()?;
                    self.expect(TT::CloseS, "")?;

                    (POSTFIX_DEFAULT_LEVEL, PostFixStateKind::ArrayIndex { index })
                }
                TT::Dot => {
                    //dot indexing
                    self.pop()?;

                    let index = self.expect_any(&[TT::IntLit, TT::Id], "dot index index")?;
                    let index = match index.ty {
                        TT::IntLit => ast::DotIndexIndex::Tuple {
                            span: index.span,
                            index: parse_int_literal(index)?,
                        },
                        TT::Id => ast::DotIndexIndex::Struct(ast::Identifier {
                            span: index.span,
                            string: index.string,
                        }),
                        _ => unreachable!(),
                    };

                    (POSTFIX_DEFAULT_LEVEL, PostFixStateKind::DotIndex { index })
                }
                TT::As => {
                    //casting
                    self.pop()?;
                    let ty = self.type_decl()?;

                    (POSTFIX_CAST_LEVEL, PostFixStateKind::Cast { ty })
                }
                _ => break
            };

            result.push(PostFixState { level, end: self.last_popped_end, kind });
        }

        Ok(result)
    }

    fn atomic(&mut self) -> Result<ast::Expression> {
        let start_pos = self.peek().span.start;

        match self.peek().ty {
            TT::IntLit => {
                let token = self.pop()?;
                let ty = self.maybe_int_ty()?;

                Ok(ast::Expression {
                    span: Span::new(token.span.start, self.last_popped_end),
                    kind: ast::ExpressionKind::IntLit { value: token.string, ty },
                })
            }
            TT::True | TT::False => {
                let token = self.pop()?;
                Ok(ast::Expression {
                    span: token.span,
                    kind: ast::ExpressionKind::BoolLit { value: token.string.parse().expect("TTs should parse correctly") },
                })
            }
            TT::Null => {
                let token = self.pop()?;
                Ok(ast::Expression {
                    span: token.span,
                    kind: ast::ExpressionKind::Null,
                })
            }
            TT::StringLit => {
                let token = self.pop()?;
                Ok(ast::Expression {
                    span: token.span,
                    kind: ast::ExpressionKind::StringLit {
                        value: token.string
                    },
                })
            }
            TT::Id => {
                let path = self.path()?;

                if !self.restrictions.no_struct_literal && self.at(TT::OpenC) {
                    return self.struct_literal(path);
                }

                Ok(ast::Expression {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::ExpressionKind::Path(path),
                })
            }
            TT::OpenB => {
                self.pop()?;
                let inner = self.unrestrict(|s| s.expression_boxed())?;
                self.expect(TT::CloseB, "closing parenthesis")?;
                Ok(ast::Expression {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::ExpressionKind::Wrapped { inner },
                })
            }
            TT::Return => {
                //TODO think about whether this is the right spot to parse a return
                self.pop()?;

                let value = if self.peek().ty == TT::Semi {
                    None
                } else {
                    Some(self.expression_boxed()?)
                };

                Ok(ast::Expression {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::ExpressionKind::Return { value },
                })
            }
            TT::Continue => {
                Ok(ast::Expression {
                    span: self.pop()?.span,
                    kind: ast::ExpressionKind::Continue,
                })
            }
            TT::Break => {
                Ok(ast::Expression {
                    span: self.pop()?.span,
                    kind: ast::ExpressionKind::Break,
                })
            }
            TT::BlackBox => {
                self.pop()?;
                self.expect(TT::OpenB, "blackbox start")?;
                let value = self.expression_boxed()?;
                self.expect(TT::CloseB, "blackbox end")?;
                Ok(ast::Expression {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::ExpressionKind::BlackBox { value },
                })
            }

            _ => Err(Self::unexpected_token(self.peek(), EXPR_START_TOKENS, "expression"))
        }
    }

    fn struct_literal(&mut self, tuple_path: ast::Path) -> Result<ast::Expression> {
        self.expect(TT::OpenC, "start of struct literal")?;

        let (_, fields) = self.list(TT::CloseC, Some(TT::Comma), |s| {
            let id = s.identifier("tuple literal field")?;
            s.expect(TT::Colon, "tuple literal field separator")?;

            let value = s.restrict(Restrictions::NO_TERNARY, |s| {
                s.expression()
            })?;

            Ok((id, value))
        })?;

        let span = Span::new(tuple_path.span.start, self.last_popped_end);
        let kind = ast::ExpressionKind::StructLiteral {
            struct_path: tuple_path,
            fields,
        };
        Ok(ast::Expression { span, kind })
    }

    fn path(&mut self) -> Result<ast::Path> {
        let mut parents = Vec::new();
        let mut id = self.identifier("identifier")?;

        while self.accept(TT::DoubleColon)?.is_some() {
            parents.push(id);
            id = self.identifier("path element")?;
        }

        let span = Span::new(id.span.start, self.last_popped_end);
        Ok(ast::Path { span, parents, id })
    }

    fn maybe_identifier(&mut self, description: &'static str) -> Result<ast::MaybeIdentifier> {
        if self.at(TT::Underscore) {
            Ok(ast::MaybeIdentifier::Placeholder(self.pop()?.span))
        } else {
            Ok(ast::MaybeIdentifier::Identifier(self.identifier(description)?))
        }
    }

    fn identifier(&mut self, description: &'static str) -> Result<ast::Identifier> {
        let token = self.expect(TT::Id, description)?;
        Ok(ast::Identifier { span: token.span, string: token.string })
    }

    fn maybe_type_decl(&mut self) -> Result<Option<ast::Type>> {
        self.accept(TT::Colon)?
            .map(|_| self.type_decl())
            .transpose()
    }

    fn maybe_int_ty(&mut self) -> Result<Option<ast::Type>> {
        let kind = match self.peek().ty {
            TT::I8 => Some(IntTypeInfo::I8),
            TT::I16 => Some(IntTypeInfo::I16),
            TT::I32 => Some(IntTypeInfo::I32),
            TT::U8 => Some(IntTypeInfo::U8),
            TT::U16 => Some(IntTypeInfo::U16),
            TT::U32 => Some(IntTypeInfo::U32),
            _ => None,
        };

        if let Some(kind) = kind {
            Ok(Some(ast::Type {
                span: self.pop()?.span,
                kind: ast::TypeKind::Int(kind),
            }))
        } else {
            Ok(None)
        }
    }

    fn type_decl(&mut self) -> Result<ast::Type> {
        let start_pos = self.peek().span.start;

        match self.peek().ty {
            TT::Underscore => Ok(ast::Type { span: self.pop()?.span, kind: ast::TypeKind::Wildcard }),

            TT::Void => Ok(ast::Type { span: self.pop()?.span, kind: ast::TypeKind::Void }),
            TT::Bool => Ok(ast::Type { span: self.pop()?.span, kind: ast::TypeKind::Bool }),

            TT::I8 | TT::I16 | TT::I32 | TT::U8 | TT::U16 | TT::U32 => Ok(self.maybe_int_ty()?.unwrap()),

            TT::Ampersand => {
                self.pop()?;
                let inner = self.type_decl()?;
                Ok(ast::Type {
                    span: Span::new(start_pos, inner.span.end),
                    kind: ast::TypeKind::Ref(Box::new(inner)),
                })
            }
            TT::Id => {
                let path = self.path()?;
                Ok(ast::Type {
                    span: path.span,
                    kind: ast::TypeKind::Path(path),
                })
            }
            TT::OpenB => {
                //func or tuple
                self.pop()?;
                let (_, list) = self.list(TT::CloseB, Some(TT::Comma), Self::type_decl)?;

                let kind = if self.accept(TT::Arrow)?.is_some() {
                    let ret = self.type_decl()?;

                    ast::TypeKind::Func {
                        params: list,
                        ret: Box::new(ret),
                    }
                } else {
                    ast::TypeKind::Tuple {
                        fields: list
                    }
                };

                Ok(ast::Type {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind,
                })
            }
            TT::OpenS => {
                //array
                self.pop()?;
                let inner = self.type_decl()?;
                self.expect(TT::Semi, "array type delimiter")?;
                let length = parse_int_literal(self.expect(TT::IntLit, "array length")?)?;
                self.expect(TT::CloseS, "end of array type")?;

                Ok(ast::Type {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::TypeKind::Array { inner: Box::new(inner), length },
                })
            }
            _ => Err(Self::unexpected_token(self.peek(), TYPE_START_TOKENS, "type declaration")),
        }
    }
}

fn parse_int_literal(token: Token) -> Result<u32> {
    token.string.parse().map_err(|e| ParseError::IntLit {
        span: token.span,
        value: token.string,
        error: e,
    })
}

pub fn parse_module(file: FileId, input: &str) -> Result<ast::ModuleContent> {
    let mut parser = Parser {
        tokenizer: Tokenizer::new(file, input)?,
        last_popped_end: Pos { file, line: 1, col: 1 },
        restrictions: Restrictions::NONE,
    };
    parser.module()
}

use std::mem::swap;

use TokenType as TT;

use crate::front::{ast, Pos, Span};
use crate::front::ast::{BinaryOp, UnaryOp};

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
    Eof {
        expected: &'static str,
    },
}

const TRIVIAL_TOKEN_LIST: &[(&str, TT)] = &[
    ("extern", TT::Extern),
    ("fun", TT::Fun),
    ("->", TT::Arrow),
    ("return", TT::Return),
    ("let", TT::Let),
    ("mut", TT::Mut),
    ("if", TT::If),
    ("else", TT::Else),
    ("while", TT::While),
    ("==", TT::DoubleEq),
    ("!=", TT::NotEq),
    (";", TT::Semi),
    (":", TT::Colon),
    (",", TT::Comma),
    ("=", TT::Eq),
    ("&", TT::Ampersand),
    ("*", TT::Star),
    ("+", TT::Plus),
    ("-", TT::Minus),
    ("/", TT::Slash),
    ("%", TT::Percent),
    ("(", TT::OpenB),
    (")", TT::CloseB),
    ("{", TT::OpenC),
    ("}", TT::CloseC),
    ("true", TT::True),
    ("false", TT::False),
    ("null", TT::Null),
];

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum TokenType {
    Id,
    IntLit,

    True,
    False,
    Null,

    Extern,
    Fun,
    Arrow,
    Return,
    Let,
    Mut,
    If,
    Else,
    While,

    NotEq,
    DoubleEq,

    Semi,
    Colon,
    Comma,
    Eq,
    Ampersand,
    Star,

    Plus,
    Minus,
    Slash,
    Percent,

    OpenB,
    CloseB,
    OpenC,
    CloseC,

    Eof,
}

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

struct Tokenizer<'a> {
    left: &'a str,
    pos: Pos,

    curr: Token,
    next: Token,
}

impl<'a> Tokenizer<'a> {
    fn new(left: &'a str) -> Self {
        let pos = Pos { line: 1, col: 1 };
        let mut result = Self {
            left,
            pos,
            curr: Token::eof_token(pos),
            next: Token::eof_token(pos),
        };
        //TODO make this not crash here, but later when actually starting to parse
        result.advance().unwrap();
        result.advance().unwrap();
        result
    }

    /// self.left should only be advanced trough this function to ensure self.pos is updated
    fn skip_fixed(&mut self, count: usize) {
        //update position
        let skipped = &self.left[0..count];
        if let Some(last_newline) = skipped.rfind('\n') {
            self.pos.col = count - last_newline;
            self.pos.line += skipped.matches('\n').count();
        } else {
            self.pos.col += count;
        }

        //actually skip
        self.left = &self.left[count..];
    }

    fn skip_past(&mut self, pattern: &'static str, allow_eof: bool) -> Result<()> {
        match self.left.find(pattern) {
            Some(i) => {
                //skip up to and including the pattern
                self.skip_fixed(i + pattern.len());
                Ok(())
            },
            None => {
                if !allow_eof { return Err(ParseError::Eof { expected: pattern }) }

                //skip to the end
                self.skip_fixed(self.left.len());
                Ok(())
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) -> Result<()> {
        loop {
            let prev_left = self.left;
            self.skip_fixed(self.left.len() - self.left.trim_start().len());

            if self.left.starts_with("//") {
                self.skip_past("\n", true)?;
            }
            if self.left.starts_with("/*") {
                self.skip_past("*/", false)?;
            }

            if prev_left == self.left { return Ok(()) }
        }
    }

    fn parse_next(&mut self) -> Result<Token> {
        self.skip_whitespace_and_comments()?;
        let start_pos = self.pos;
        if self.left.is_empty() { return Ok(Token::eof_token(start_pos)) }

        for (pattern, ty) in TRIVIAL_TOKEN_LIST {
            if self.left.starts_with(pattern) {
                self.skip_fixed(pattern.len());
                let end_pos = self.pos;
                return Ok(Token {
                    ty: *ty,
                    string: pattern.to_string(),
                    span: Span::new(start_pos, end_pos),
                });
            }
        }

        let mut chars = self.left.chars().peekable();

        //number
        if chars.peek().unwrap().is_ascii_digit() {
            let string: String = chars.take_while(|&c| c.is_ascii_digit()).collect();
            self.skip_fixed(string.len());
            let end_pos = self.pos;
            return Ok(Token {
                ty: TT::IntLit,
                string,
                span: Span::new(start_pos, end_pos),
            });
        }

        //identifier
        let c = *chars.peek().unwrap();
        if c.is_ascii_alphabetic() || c == '_' {
            let string: String = chars.take_while(|&c| c.is_ascii_alphanumeric() || c == '_' || c == '@').collect();
            self.skip_fixed(string.len());
            let end_pos = self.pos;
            return Ok(Token {
                ty: TT::Id,
                string,
                span: Span::new(start_pos, end_pos),
            });
        }

        Err(ParseError::Char {
            pos: self.pos,
            char: self.left.chars().next().unwrap(), //eof was handled earlier
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

struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
    last_popped_end: Pos,
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

struct BinOpInfo {
    level: u8,
    token: TT,
    bind_left: bool,
    op: BinaryOp,
}

impl BinOpInfo {
    const fn new(level: u8, token: TokenType, bind_left: bool, op: BinaryOp) -> Self {
        Self { level, token, bind_left, op }
    }
}

const BINARY_OPERATOR_INFO: &[BinOpInfo] = &[
    BinOpInfo::new(3, TT::DoubleEq, true, BinaryOp::Eq),
    BinOpInfo::new(3, TT::NotEq, true, BinaryOp::Neq),
    BinOpInfo::new(5, TT::Plus, true, BinaryOp::Add),
    BinOpInfo::new(5, TT::Minus, true, BinaryOp::Sub),
    BinOpInfo::new(6, TT::Slash, true, BinaryOp::Div),
    BinOpInfo::new(6, TT::Star, true, BinaryOp::Mul),
    BinOpInfo::new(6, TT::Percent, true, BinaryOp::Mod),
];

struct UnOpInfo {
    token: TT,
    op: UnaryOp,
}

impl UnOpInfo {
    const fn new(token: TokenType, op: UnaryOp) -> Self {
        UnOpInfo { token, op }
    }
}

const PREFIX_UNARY_OPERATOR_INFO: &[UnOpInfo] = &[
    UnOpInfo::new(TT::Ampersand, UnaryOp::Ref),
    UnOpInfo::new(TT::Star, UnaryOp::Deref),
    UnOpInfo::new(TT::Minus, UnaryOp::Neg),
];

#[allow(dead_code)]
impl<'a> Parser<'a> {
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
            self.pop().map(Option::Some)
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

            if self.accept(end)?.is_some() { break }

            if let Some(sep) = sep {
                self.expect(sep, "separator")?;
            }
        }

        Ok((Span::new(start_pos, end_pos), result))
    }
}

impl<'a> Parser<'a> {
    fn program(&mut self) -> Result<ast::Program> {
        let (_, items) = self.list(TT::Eof, None, Self::item)?;
        Ok(ast::Program { items })
    }

    fn item(&mut self) -> Result<ast::Item> {
        let token = self.peek();

        match token.ty {
            TT::Fun | TT::Extern => self.function().map(ast::Item::Function),
            _ => Err(Self::unexpected_token(token, &[TT::Fun], "start of item"))
        }
    }

    fn function(&mut self) -> Result<ast::Function> {
        let start_pos = self.peek().span.start;

        let ext = self.accept(TT::Extern)?.is_some();
        self.expect(TT::Fun, "function declaration")?;
        let id = self.identifier()?;

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
        let id = self.identifier()?;
        self.expect(TT::Colon, "parameter type")?;
        let ty = self.type_decl()?;

        let span = Span::new(id.span.start, ty.span.end);
        Ok(ast::Parameter { span, id, ty })
    }

    fn block(&mut self) -> Result<ast::Block> {
        let start_pos = self.expect(TT::OpenC, "start of block")?.span.start;
        let (span, statements) = self.list(TT::CloseC, None,Self::statement)?;

        Ok(ast::Block { span: Span::new(start_pos, span.end), statements })
    }

    fn statement(&mut self) -> Result<ast::Statement> {
        let token = self.peek();
        let start_pos = token.span.start;

        let (kind, need_semi) = match token.ty {
            TT::Let => {
                //declaration
                let decl = self.variable_declaration()?;
                (ast::StatementKind::Declaration(decl), true)
            },
            TT::If => {
                self.pop()?;
                let cond = self.expression()?;
                let then_block = self.block()?;

                let else_block = self.accept(TT::Else)?
                    .map(|_| self.block())
                    .transpose()?;

                (ast::StatementKind::If(ast::IfStatement {
                    span: Span::new(start_pos, self.last_popped_end),
                    cond: Box::new(cond),
                    then_block,
                    else_block,
                }), false)
            },
            TT::While => {
                self.pop()?;

                let cond = self.expression()?;
                let body = self.block()?;

                (ast::StatementKind::While(ast::WhileStatement {
                    span: Span::new(start_pos, self.last_popped_end),
                    cond: Box::new(cond),
                    body,
                }), false)
            },
            TT::OpenC => {
                (ast::StatementKind::Block(self.block()?), false)
            },
            _ => {
                let left = self.expression()?;

                let kind = if self.accept(TT::Eq)?.is_some() {
                    //assignment
                    let right = self.expression()?;
                    ast::StatementKind::Assignment(ast::Assignment {
                        span: Span::new(left.span.start, right.span.end),
                        left: Box::new(left),
                        right: Box::new(right),
                    })
                } else {
                    // expression
                    ast::StatementKind::Expression(Box::new(left))
                };

                (kind, true)
            },
        };

        if need_semi {
            self.expect(TT::Semi, "end of statement")?.span.end;
        }

        let span = Span::new(start_pos, self.last_popped_end);
        Ok(ast::Statement { span, kind })
    }

    fn variable_declaration(&mut self) -> Result<ast::Declaration> {
        let start_pos = self.expect(TT::Let, "variable declaration")?.span.start;
        let mutable = self.accept(TT::Mut)?.is_some();
        let id = self.identifier()?;

        let ty = self.accept(TT::Colon)?
            .map(|_| self.type_decl())
            .transpose()?;
        let init = self.accept(TT::Eq)?
            .map(|_| self.expression().map(Box::new))
            .transpose()?;

        Ok(ast::Declaration { span: Span::new(start_pos, self.last_popped_end), mutable, ty, id, init })
    }

    fn expression(&mut self) -> Result<ast::Expression> {
        self.precedence_climb_binop(0)
    }

    fn precedence_climb_binop(&mut self, lower_level: u8) -> Result<ast::Expression> {
        let mut curr = self.unary()?;

        loop {
            let token = self.peek();
            let info = BINARY_OPERATOR_INFO.iter()
                .find(|i| i.token == token.ty);

            if let Some(info) = info {
                if info.level < lower_level { break }
                self.pop()?;

                let next_lower_level = info.level + (info.bind_left as u8);
                let right = self.precedence_climb_binop(next_lower_level)?;

                curr = ast::Expression {
                    span: Span::new(curr.span.start, right.span.end),
                    kind: ast::ExpressionKind::Binary {
                        kind: info.op,
                        left: Box::new(curr),
                        right: Box::new(right),
                    },
                }
            } else {
                break
            }
        }

        Ok(curr)
    }

    fn unary(&mut self) -> Result<ast::Expression> {
        //prefix
        let mut prefix_ops = Vec::new();
        loop {
            let token = self.peek();
            let info = PREFIX_UNARY_OPERATOR_INFO.iter()
                .find(|i| i.token == token.ty);
            if let Some(info) = info {
                let token = self.pop()?;
                prefix_ops.push((token.span.start, info.op));
            } else {
                break
            }
        }

        //inner expression
        let mut curr = self.atomic()?;

        //postfix, apply immediately from left to right
        loop {
            let token = self.peek();

            match token.ty {
                TT::OpenB => {
                    //call
                    self.pop()?;
                    let (_, args) = self.list(TT::CloseB, Some(TT::Comma), Self::expression)?;
                    let span = Span::new(curr.span.start, self.last_popped_end);
                    curr = ast::Expression {
                        span,
                        kind: ast::ExpressionKind::Call {
                            target: Box::new(curr),
                            args,
                        },
                    }
                }
                _ => break
            }
        }

        //apply prefixes from right to left
        for (pos, op) in prefix_ops {
            curr = ast::Expression {
                span: Span::new(pos, curr.span.end),
                kind: ast::ExpressionKind::Unary {
                    kind: op,
                    inner: Box::new(curr),
                },
            }
        }

        Ok(curr)
    }

    fn atomic(&mut self) -> Result<ast::Expression> {
        let start_pos = self.peek().span.start;

        match self.peek().ty {
            TT::IntLit | TT::True | TT::False | TT::Null => {
                let token = self.pop()?;
                Ok(ast::Expression {
                    span: token.span,
                    kind: ast::ExpressionKind::Literal { value: token.string },
                })
            }
            TT::Id => {
                let token = self.pop()?;
                Ok(ast::Expression {
                    span: token.span,
                    kind: ast::ExpressionKind::Identifier {
                        id: ast::Identifier { span: token.span, string: token.string }
                    },
                })
            }
            TT::OpenB => {
                self.pop()?;
                let expr = self.expression()?;
                self.expect(TT::CloseB, "closing parenthesis")?;
                Ok(expr)
            }
            TT::Return => {
                //TODO think about whether this is the right spot to parse a return
                self.pop()?;

                let value = if self.peek().ty == TT::Semi {
                    None
                } else {
                    Some(Box::new(self.expression()?))
                };

                Ok(ast::Expression {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::ExpressionKind::Return { value },
                })
            }
            _ => Err(Self::unexpected_token(self.peek(), EXPR_START_TOKENS, "expression"))
        }
    }

    fn identifier(&mut self) -> Result<ast::Identifier> {
        let token = self.expect(TT::Id, "identifier")?;
        Ok(ast::Identifier { span: token.span, string: token.string })
    }

    fn type_decl(&mut self) -> Result<ast::Type> {
        let start_pos = self.peek().span.start;
        match self.peek().ty {
            TT::Ampersand => {
                self.pop()?;
                let inner = self.type_decl()?;
                Ok(ast::Type {
                    span: Span::new(start_pos, inner.span.end),
                    kind: ast::TypeKind::Ref(Box::new(inner)),
                })
            },
            TT::Id => {
                let token = self.pop()?;
                Ok(ast::Type {
                    span: token.span,
                    kind: ast::TypeKind::Simple(token.string),
                })
            },
            TT::OpenB => {
                self.pop()?;
                let (_, params) = self.list(TT::CloseB, Some(TT::Comma), Self::type_decl)?;
                self.expect(TT::Arrow, "return type separator")?;
                let ret = self.type_decl()?;

                Ok(ast::Type {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::TypeKind::Func {
                        params,
                        ret: Box::new(ret),
                    },
                })
            }
            _ => Err(Self::unexpected_token(self.peek(), &[TT::Ampersand, TT::Id, TT::OpenB], "type declaration")),
        }
    }
}

pub fn parse(input: &str) -> Result<ast::Program> {
    let mut parser = Parser {
        tokenizer: Tokenizer::new(input),
        last_popped_end: Pos { line: 1, col: 1 },
    };
    parser.program()
}
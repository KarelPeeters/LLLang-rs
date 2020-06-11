use std::mem::swap;

use TokenType as TT;

use crate::front::{ast, Pos, Span};

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
    Eof,
}

const TRIVIAL_TOKEN_LIST: &[(&str, TT)] = &[
    ("fun", TT::Fun),
    ("->", TT::Arrow),
    ("return", TT::Return),
    ("let", TT::Let),
    ("mut", TT::Mut),
    ("if", TT::If),
    ("else", TT::Else),
    (";", TT::Semi),
    (":", TT::Colon),
    ("=", TT::Eq),
    ("&", TT::Ampersand),
    ("*", TT::Star),
    ("(", TT::OpenB),
    (")", TT::CloseB),
    ("{", TT::OpenC),
    ("}", TT::CloseC),
    ("true", TT::True),
    ("false", TT::False),
];

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum TokenType {
    Id,
    IntLit,

    True,
    False,

    Fun,
    Arrow,
    Return,
    Let,
    Mut,
    If,
    Else,

    Semi,
    Colon,
    Eq,
    Ampersand,
    Star,

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

    fn skip_past(&mut self, pattern: &str, allow_eof: bool) -> Result<()> {
        let index = match self.left.find(pattern) {
            Some(i) => i,
            None => {
                return if allow_eof { Ok(()) } else { Err(ParseError::Eof) }
            }
        };

        self.skip_fixed(index + pattern.len());
        Ok(())
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
        if chars.peek().unwrap().is_ascii_alphabetic() {
            let string: String = chars.take_while(|&c| c.is_ascii_alphanumeric() || c == '_').collect();
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
            Err(self.unexpected_token(
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
            Err(self.unexpected_token(self.peek(), tys, description))
        }
    }

    fn unexpected_token(&self, token: &Token, allowed: &[TT], description: &'static str) -> ParseError {
        ParseError::Token {
            ty: token.ty,
            pos: token.span.start,
            allowed: allowed.iter().copied().collect(),
            description,
        }
    }
}

impl<'a> Parser<'a> {
    fn function(&mut self) -> Result<ast::Function> {
        let start_pos = self.expect(TT::Fun, "function declaration")?.span.start;
        let id = self.identifier()?;
        self.expect_all(&[TT::OpenB, TT::CloseB, TT::Arrow], "function header")?;
        let ret_ty = self.type_decl()?;
        let body = self.block()?;

        Ok(ast::Function {
            span: Span::new(start_pos, body.span.end),
            id,
            ret_type: ret_ty,
            body,
        })
    }

    fn block(&mut self) -> Result<ast::Block> {
        let start_pos = self.expect(TT::OpenC, "start of block")?.span.start;

        let mut statements = Vec::new();

        while self.accept(TT::CloseC)?.is_none() {
            statements.push(self.statement()?)
        }

        Ok(ast::Block {
            span: Span::new(start_pos, self.last_popped_end),
            statements,
        })
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
            TT::OpenC => {
                (ast::StatementKind::Block(self.block()?), false)
            }
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
            }
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
        //TODO maybe change this pop into some accept-like structure?
        let token = self.pop()?;

        let (kind, kind_span) = match token.ty {
            TT::Return => {
                let value = self.expression()?;
                let span = Span::new(token.span.start, value.span.end);
                (ast::ExpressionKind::Return { value: Box::new(value) }, span)
            }
            TT::IntLit | TT::True | TT::False => {
                (ast::ExpressionKind::Literal { value: token.string }, token.span)
            }
            TT::Id => {
                (ast::ExpressionKind::Identifier { id: ast::Identifier { span: token.span, string: token.string } }, token.span)
            }
            TT::Ampersand => {
                let expr = self.expression()?;
                let span = Span::new(token.span.start, expr.span.end);
                (ast::ExpressionKind::Ref { inner: Box::new(expr) }, span)
            }
            TT::Star => {
                let expr = self.expression()?;
                let span = Span::new(token.span.start, expr.span.end);
                (ast::ExpressionKind::DeRef { inner: Box::new(expr) }, span)
            }
            _ => return Err(self.unexpected_token(
                &token,
                &[TT::Return, TT::IntLit, TT::True, TT::False, TT::Id, TT::Ampersand, TT::Star],
                "expression",
            ))
        };

        Ok(ast::Expression {
            span: Span::new(token.span.start, kind_span.end),
            kind,
        })
    }

    fn identifier(&mut self) -> Result<ast::Identifier> {
        let token = self.expect(TT::Id, "identifier")?;
        Ok(ast::Identifier { span: token.span, string: token.string })
    }

    fn type_decl(&mut self) -> Result<ast::Type> {
        let amper = self.accept(TT::Ampersand)?;
        if let Some(amper) = amper {
            let inner = self.type_decl()?;
            Ok(ast::Type {
                span: Span::new(amper.span.start, inner.span.end),
                kind: ast::TypeKind::Ref(Box::new(inner)),
            })
        } else {
            let token = self.expect(TT::Id, "type declaration")?;
            Ok(ast::Type {
                span: token.span,
                kind: ast::TypeKind::Simple(token.string),
            })
        }
    }
}

pub fn parse(input: &str) -> Result<ast::Function> {
    let mut parser = Parser {
        tokenizer: Tokenizer::new(input),
        last_popped_end: Pos { line: 1, col: 1 },
    };
    parser.function()
}
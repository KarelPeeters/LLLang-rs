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
    (";", TT::Semi),
    (":", TT::Colon),
    ("=", TT::Eq),
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

    Semi,
    Colon,
    Eq,

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
                return if allow_eof { Ok(()) } else { Err(ParseError::Eof) };
            }
        };

        self.skip_fixed(index);
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

            if prev_left == self.left { return Ok(()); }
        }
    }

    fn parse_next(&mut self) -> Result<Token> {
        self.skip_whitespace_and_comments()?;
        let start_pos = self.pos;
        if self.left.is_empty() { return Ok(Token::eof_token(start_pos)); }

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

    pub fn advance(&mut self) -> Result<Token> {
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
}

#[allow(dead_code)]
impl<'a> Parser<'a> {
    fn pop(&mut self) -> Result<Token> {
        self.tokenizer.advance()
    }

    fn curr(&self) -> &Token {
        &self.tokenizer.curr
    }

    fn lookahead(&self) -> &Token {
        &self.tokenizer.next
    }

    fn at(&mut self, ty: TT) -> bool {
        self.curr().ty == ty
    }

    fn accept(&mut self, ty: TT) -> Result<Option<Token>> {
        if self.at(ty) {
            self.pop().map(Option::Some)
        } else {
            Ok(None)
        }
    }

    fn expect(&mut self, ty: TT, description: &'static str) -> Result<Token> {
        if self.at(ty) {
            self.pop()
        } else {
            Err(self.unexpected_token(
                &[ty],
                description,
            ))
        }
    }

    fn expect_all(&mut self, tys: &[TT], description: &'static str) -> Result<()> {
        for &ty in tys {
            self.expect(ty, description)?;
        }
        Ok(())
    }

    fn expect_any(&mut self, tys: &'static [TT], description: &'static str) -> Result<Token> {
        if tys.contains(&self.curr().ty) {
            Ok(self.pop()?)
        } else {
            Err(self.unexpected_token(tys, description))
        }
    }

    fn unexpected_token(&self, allowed: &[TT], description: &'static str) -> ParseError {
        ParseError::Token {
            ty: self.curr().ty,
            pos: self.curr().span.start,
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
        let ret_ty = self.type_name()?;
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

        let end_pos = loop {
            if let Some(end) = self.accept(TT::CloseC)? {
                break end.span.end;
            }
            statements.push(self.statement()?)
        };

        Ok(ast::Block {
            span: Span::new(start_pos, end_pos),
            statements,
        })
    }

    fn statement(&mut self) -> Result<ast::Statement> {
        let (kind, start_pos) = if self.at(TT::Let) {
            //declaration
            let decl = self.variable_declaration()?;
            let start = decl.span.start;
            (ast::StatementKind::Declaration(decl), start)
        } else {
            let left = self.expression()?;
            let start_pos = left.span.start;

            let stmt = if self.accept(TT::Eq)?.is_some() {
                //assignment
                let right = self.expression()?;
                ast::StatementKind::Assignment(ast::Assignment {
                    span: Span::new(start_pos, right.span.end),
                    left: Box::new(left),
                    right: Box::new(right),
                })
            } else {
                // expression
                ast::StatementKind::Expression(Box::new(left))
            };

            (stmt, start_pos)
        };

        let end = self.expect(TT::Semi, "end of statement")?.span.end;
        let span = Span::new(start_pos, end);

        Ok(ast::Statement { span, kind })
    }

    fn variable_declaration(&mut self) -> Result<ast::Declaration> {
        let start_pos = self.expect(TT::Let, "variable declaration")?.span.start;
        let mutable = self.accept(TT::Mut)?.is_some();
        let id = self.identifier()?;
        let mut end_pos = id.span.end;

        let ty = if self.accept(TT::Colon)?.is_some() {
            let ty = self.type_name()?;
            end_pos = ty.span.end;
            Some(ty)
        } else {
            None
        };
        let init = if self.accept(TT::Eq)?.is_some() {
            let expr = self.expression()?;
            end_pos = expr.span.end;
            Some(Box::new(expr))
        } else {
            None
        };

        Ok(ast::Declaration { span: Span::new(start_pos, end_pos), mutable, ty, id, init })
    }

    fn expression(&mut self) -> Result<ast::Expression> {
        //TODO maybe change this pop into some accept-like structure?
        let token = self.pop()?;

        let (kind, kind_span) = match token.ty {
            TT::Return => {
                let value = self.expression()?;
                let span = value.span;
                (ast::ExpressionKind::Return { value: Box::new(value) }, span)
            }
            TT::IntLit | TT::True | TT::False => {
                (ast::ExpressionKind::Literal { value: token.string }, token.span)
            }
            TT::Id => {
                (ast::ExpressionKind::Identifier { id: ast::Identifier { span: token.span, string: token.string } }, token.span)
            }
            _ => return Err(self.unexpected_token(
                &[TT::Return, TT::IntLit, TT::True, TT::False, TT::Id],
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


    fn type_name(&mut self) -> Result<ast::Type> {
        let token = self.expect(TT::Id, "type declaration")?;
        Ok(ast::Type { span: token.span, string: token.string })
    }
}

pub fn parse(input: &str) -> Result<ast::Function> {
    let mut parser = Parser { tokenizer: Tokenizer::new(input) };
    parser.function()
}
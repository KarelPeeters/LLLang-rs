use std::mem::swap;

use TokenType as TT;

use crate::front::{ast, Pos, Span};
use crate::front::ast::{Block, StatementKind};

type Result<T> = std::result::Result<T, ()>;

const TRIVIAL_TOKEN_LIST: &[(&str, TT)] = &[
    ("fun", TT::Fun),
    ("->", TT::Arrow),
    ("return", TT::Return),
    (";", TT::Semi),
    ("(", TT::OpenB),
    (")", TT::CloseB),
    ("{", TT::OpenC),
    ("}", TT::CloseC),
    ("true", TT::True),
    ("false", TT::False),
];

#[allow(unused)]
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum TokenType {
    Id,
    IntLit,

    True,
    False,

    Fun,
    Arrow,
    Return,

    Semi,
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
            span: Span::empty(pos),
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
                return if allow_eof { Ok(()) } else { Err(()) };
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

        Err(())
    }

    pub fn advance(&mut self) -> Result<Token> {
        let next = self.parse_next()?;
        println!("{:?}", next);

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

#[allow(unused)]
impl<'a> Parser<'a> {
    fn pop(&mut self) -> Result<Token> {
        self.tokenizer.advance()
    }

    fn curr(&self) -> &Token {
        &self.tokenizer.curr
    }

    fn next(&self) -> &Token {
        &self.tokenizer.next
    }

    fn accept(&mut self, token: TT) -> Result<Option<Token>> {
        if self.curr().ty == token {
            self.pop().map(Option::Some)
        } else {
            Ok(None)
        }
    }

    fn expect(&mut self, ty: TT) -> Result<Token> {
        if self.curr().ty == ty {
            self.pop()
        } else {
            Err(())
        }
    }

    fn expect_all(&mut self, tys: &[TT]) -> Result<()> {
        for &ty in tys {
            self.expect(ty)?;
        }
        Ok(())
    }

    fn expect_any(&mut self, tys: &[TT]) -> Result<Token> {
        if tys.contains(&self.curr().ty) {
            Ok(self.pop()?)
        } else {
            Err(())
        }
    }
}

impl<'a> Parser<'a> {
    fn function(&mut self) -> Result<ast::Function> {
        let start_pos = self.expect(TT::Fun)?.span.start;
        let name = self.expect(TT::Id)?.string;
        self.expect_all(&[TT::OpenB, TT::CloseB, TT::Arrow])?;

        let ret_type = self.expect(TT::Id)?;
        let ret_type = ast::TypeDecl { span: ret_type.span, string: ret_type.string };

        let body = self.block()?;

        Ok(ast::Function {
            span: Span::new(start_pos, body.span.end),
            name,
            ret_type,
            body,
        })
    }

    fn block(&mut self) -> Result<ast::Block> {
        let start_pos = self.expect(TT::OpenC)?.span.start;
        let mut statements = Vec::new();

        loop {
            if let Some(end) = self.accept(TT::CloseC)? {
                return Ok(Block { span: Span::new(start_pos, end.span.end), statements });
            }

            statements.push(self.statement()?);
        }
    }

    fn statement(&mut self) -> Result<ast::Statement> {
        if let Some(ret) = self.accept(TT::Return)? {
            let value = self.expect_any(&[TT::IntLit, TT::True, TT::False])?;
            let value = ast::Value { span: value.span, value: value.string };
            let semi = self.expect(TT::Semi)?;

            Ok(ast::Statement {
                span: Span::new(ret.span.start, semi.span.end),
                kind: StatementKind::Return { value },
            })
        } else {
            Err(())
        }
    }
}

pub fn parse(input: &str) -> Result<ast::Function> {
    let mut parser = Parser { tokenizer: Tokenizer::new(input) };
    parser.function()
}
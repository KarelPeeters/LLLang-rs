use std::mem::swap;

use TokenType as TT;

use crate::mid::ir;
use crate::mid::ir::Function;

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
    ("i32", TT::I32),
];

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum TokenType {
    Id,
    IntLit,

    Fun,
    Arrow,
    Return,

    Semi,
    OpenB,
    CloseB,
    OpenC,
    CloseC,

    I32,

    Eof,
}

#[derive(Eq, PartialEq, Clone, Debug)]
struct Token {
    ty: TT,
    string: String,
}

impl Token {
    fn eof_token() -> Token {
        Token {
            ty: TT::Eof,
            string: "".to_string(),
        }
    }
}

struct Tokenizer<'a> {
    left: &'a str,

    curr: Token,
    next: Token,
}

impl<'a> Tokenizer<'a> {
    fn new(left: &'a str) -> Self {
        let mut result = Self {
            left,
            curr: Token::eof_token(),
            next: Token::eof_token(),
        };
        //TODO make this not crash here, but later when actually starting to parse
        result.advance().unwrap();
        result.advance().unwrap();
        result
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

    fn skip_fixed(&mut self, count: usize) {
        self.left = &self.left[count..];
    }

    fn skip_whitespace_and_comments(&mut self) -> Result<()> {
        loop {
            let prev_left = self.left;
            self.left = self.left.trim_start();

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
        if self.left.is_empty() { return Ok(Token::eof_token()); }

        for (pattern, ty) in TRIVIAL_TOKEN_LIST {
            if self.left.starts_with(pattern) {
                self.skip_fixed(pattern.len());
                return Ok(Token { ty: *ty, string: pattern.to_string() });
            }
        }

        let mut chars = self.left.chars().peekable();

        //number
        if chars.peek().unwrap().is_ascii_digit() {
            let string: String = chars.take_while(|&c| c.is_ascii_digit()).collect();
            self.skip_fixed(string.len());
            return Ok(Token { ty: TT::IntLit, string });
        }

        //identifier
        if chars.peek().unwrap().is_ascii_alphabetic() {
            let string: String = chars.take_while(|&c| c.is_ascii_alphanumeric() || c == '_').collect();
            self.skip_fixed(string.len());
            return Ok(Token { ty: TT::Id, string });
        }

        Err(())
    }

    pub fn advance(&mut self) -> Result<Token> {
        let next = self.parse_next()?;
        let mut result = Token::eof_token();

        swap(&mut result, &mut self.curr);
        swap(&mut self.curr, &mut self.next);

        self.next = next;
        Ok(result)
    }
}

struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
}

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
}

impl<'a> Parser<'a> {
    fn function(&mut self) -> Result<ir::Function> {
        self.expect(TT::Fun)?;
        let name = self.expect(TT::Id)?.string;
        self.expect_all(&[TT::OpenB, TT::CloseB, TT::Arrow, TT::I32])?;
        let body = self.block()?;

        Ok(Function {
            name,
            body,
        })
    }

    fn block(&mut self) -> Result<ir::Block> {
        self.expect(TT::OpenC)?;
        let mut statements = Vec::new();
        while self.accept(TT::CloseC)?.is_none() {
            statements.push(self.statement()?);
        }
        Ok(ir::Block { statements })
    }

    fn statement(&mut self) -> Result<ir::Statement> {
        if self.accept(TT::Return)?.is_some() {
            if let Token { ty: TT::IntLit, string } = self.pop()? {
                self.expect(TT::Semi)?;
                Ok(ir::Statement::Return {
                    //TODO handle this error
                    //TODO think about whether - should be part of literals, makes const easier
                    value: string.parse().unwrap(),
                })
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

pub fn parse(input: &str) -> Result<ir::Function> {
    let mut parser = Parser { tokenizer: Tokenizer::new(input) };
    parser.function()
}
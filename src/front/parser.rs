use std::mem::swap;

use TokenType as TT;

use crate::front::ast;
use crate::front::pos::{Pos, FileId, Span};
use crate::front::ast::{DotIndexIndex, Identifier};

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
        after: Pos,
        expected: &'static str,
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

    //TODO remove these as tokens and just handle them as paths?
    True("true"),
    False("false"),
    Null("null"),

    Extern("extern"),
    Use("use"),
    Struct("struct"),
    Fun("fun"),
    Return("return"),
    Let("let"),
    Const("const"),
    Mut("mut"),
    If("if"),
    Else("else"),
    While("while"),
    For("for"),
    In("in"),
    Break("break"),
    Continue("continue"),

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

    Dot("."),
    DoubleColon("::"),
    Semi(";"),
    Colon(":"),
    QuestionMark("?"),
    Comma(","),
    Eq("="),
    Ampersand("&"),
    Star("*"),

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

struct Tokenizer<'a> {
    left: &'a str,
    file: FileId,
    pos: Pos,

    curr: Token,
    next: Token,
}

impl<'a> Tokenizer<'a> {
    fn new(file: FileId, left: &'a str) -> Result<Self> {
        let pos = Pos { file, line: 1, col: 1 };
        let mut result = Self {
            file,
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

    fn parse_next(&mut self) -> Result<Token> {
        self.skip_whitespace_and_comments()?;
        let start_pos = self.pos;

        let peek = if let Some(peek) = self.left.chars().next() {
            peek
        } else {
            return Ok(Token::eof_token(start_pos));
        };

        //number
        if peek.is_ascii_digit() {
            let end = self.left
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(self.left.len());
            let string = self.skip_count(end).to_owned();

            return Ok(Token {
                ty: TT::IntLit,
                string,
                span: Span::new(start_pos, self.pos),
            });
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
    op: ast::BinaryOp,
}

impl BinOpInfo {
    const fn new(level: u8, token: TokenType, bind_left: bool, op: ast::BinaryOp) -> Self {
        Self { level, token, bind_left, op }
    }
}

const BINARY_OPERATOR_INFO: &[BinOpInfo] = &[
    BinOpInfo::new(3, TT::DoubleEq, true, ast::BinaryOp::Eq),
    BinOpInfo::new(3, TT::NotEq, true, ast::BinaryOp::Neq),
    BinOpInfo::new(3, TT::GreaterEqual, true, ast::BinaryOp::Gte),
    BinOpInfo::new(3, TT::Greater, true, ast::BinaryOp::Gt),
    BinOpInfo::new(3, TT::LessEqual, true, ast::BinaryOp::Lte),
    BinOpInfo::new(3, TT::Less, true, ast::BinaryOp::Lt),
    BinOpInfo::new(5, TT::Plus, true, ast::BinaryOp::Add),
    BinOpInfo::new(5, TT::Minus, true, ast::BinaryOp::Sub),
    BinOpInfo::new(6, TT::Slash, true, ast::BinaryOp::Div),
    BinOpInfo::new(6, TT::Star, true, ast::BinaryOp::Mul),
    BinOpInfo::new(6, TT::Percent, true, ast::BinaryOp::Mod),
];

struct UnOpInfo {
    token: TT,
    op: ast::UnaryOp,
}

impl UnOpInfo {
    const fn new(token: TokenType, op: ast::UnaryOp) -> Self {
        UnOpInfo { token, op }
    }
}

const PREFIX_UNARY_OPERATOR_INFO: &[UnOpInfo] = &[
    UnOpInfo::new(TT::Ampersand, ast::UnaryOp::Ref),
    UnOpInfo::new(TT::Star, ast::UnaryOp::Deref),
    UnOpInfo::new(TT::Minus, ast::UnaryOp::Neg),
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

            if self.accept(end)?.is_some() { break; }

            if let Some(sep) = sep {
                self.expect(sep, "separator")?;
            }
        }

        Ok((Span::new(start_pos, end_pos), result))
    }
}

impl<'a> Parser<'a> {
    fn module(&mut self) -> Result<ast::Module> {
        let (_, items) = self.list(TT::Eof, None, Self::item)?;
        Ok(ast::Module { items })
    }

    fn item(&mut self) -> Result<ast::Item> {
        let token = self.peek();
        let start = token.span.start;

        match token.ty {
            TT::Struct => self.struct_().map(ast::Item::Struct),
            TT::Fun | TT::Extern => self.function().map(ast::Item::Function),
            TT::Const => {
                let decl = self.variable_declaration(TT::Const)?;
                self.expect(TT::Semi, "end of item")?;
                Ok(ast::Item::Const(decl))
            }
            TT::Use => {
                self.pop()?;
                let module = self.identifier("module name")?;
                self.expect(TT::Semi, "end of item")?;

                Ok(ast::Item::UseDecl(ast::UseDecl {
                    span: Span::new(start, module.span.end),
                    module,
                }))
            }
            _ => Err(Self::unexpected_token(token, &[TT::Struct, TT::Fun, TT::Extern, TT::Const, TT::Use], "start of item"))
        }
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
        self.expect(TT::Fun, "function declaration")?;
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
        let id = self.identifier("parameter name")?;
        self.expect(TT::Colon, "parameter type")?;
        let ty = self.type_decl()?;

        let span = Span::new(id.span.start, ty.span.end);
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
            }
            TT::While => {
                self.pop()?;

                let cond = Box::new(self.expression()?);
                let body = self.block()?;

                let span = Span::new(start_pos, self.last_popped_end);
                (ast::StatementKind::While(ast::WhileStatement { span, cond, body }), false)
            }
            TT::For => {
                self.pop()?;

                let index = self.identifier("index variable")?;
                let index_ty = self.maybe_type_decl()?;

                self.expect(TT::In, "in")?;
                let start = Box::new(self.expression()?);
                self.expect(TT::DoubleDot, "range separator")?;
                let end = Box::new(self.expression()?);

                let body = self.block()?;

                let span = Span::new(start_pos, self.last_popped_end);
                (ast::StatementKind::For(ast::ForStatement { span, index, index_ty, start, end, body }), false)
            }
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
                    //expression
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

    fn variable_declaration(&mut self, ty: TT) -> Result<ast::Declaration> {
        let start_pos = self.expect(ty, "variable declaration")?.span.start;
        let mutable = self.accept(TT::Mut)?.is_some();
        let id = self.identifier("variable name")?;

        let ty = self.maybe_type_decl()?;
        let init = self.accept(TT::Eq)?
            .map(|_| self.expression().map(Box::new))
            .transpose()?;

        Ok(ast::Declaration { span: Span::new(start_pos, self.last_popped_end), mutable, ty, id, init })
    }

    fn expression(&mut self) -> Result<ast::Expression> {
        let expr = self.precedence_climb_binop(0)?;
        let start = expr.span.start;

        if self.accept(TT::QuestionMark)?.is_some() {
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

    fn precedence_climb_binop(&mut self, lower_level: u8) -> Result<ast::Expression> {
        let mut curr = self.unary()?;

        loop {
            let token = self.peek();
            let info = BINARY_OPERATOR_INFO.iter()
                .find(|i| i.token == token.ty);

            if let Some(info) = info {
                if info.level < lower_level { break; }
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
                break;
            }
        }

        Ok(curr)
    }

    fn unary(&mut self) -> Result<ast::Expression> {
        //prefix, will be applied later from right to left
        let mut prefix_ops = Vec::new();
        loop {
            let token = self.peek();
            let info = PREFIX_UNARY_OPERATOR_INFO.iter()
                .find(|i| i.token == token.ty);
            if let Some(info) = info {
                let token = self.pop()?;
                prefix_ops.push((token.span.start, info.op));
            } else {
                break;
            }
        }

        //inner expression
        let mut curr = self.atomic()?;
        let curr_start = curr.span.start;

        //postfix, apply immediately from left to right
        loop {
            let token = self.peek();

            let kind = match token.ty {
                TT::OpenB => {
                    //call
                    self.pop()?;
                    let (_, args) = self.list(TT::CloseB, Some(TT::Comma), Self::expression)?;
                    ast::ExpressionKind::Call {
                        target: Box::new(curr),
                        args,
                    }
                }
                TT::Dot => {
                    //dot indexing
                    self.pop()?;
                    
                    let index = self.expect_any(&[TT::IntLit, TT::Id], "dot index index")?;
                    let index = match index.ty {
                        //TODO proper IntLit parsing
                        TT::IntLit => DotIndexIndex::Tuple { span: index.span, index: index.string },
                        TT::Id => DotIndexIndex::Struct(Identifier { span: index.span, string: index.string }),
                        _ => unreachable!(),
                    };

                    ast::ExpressionKind::DotIndex {
                        target: Box::new(curr),
                        index,
                    }
                }
                _ => break
            };

            curr = ast::Expression {
                span: Span::new(curr_start, self.last_popped_end),
                kind,
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
            TT::IntLit => {
                let token = self.pop()?;
                Ok(ast::Expression {
                    span: token.span,
                    kind: ast::ExpressionKind::IntLit { value: token.string },
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
                Ok(ast::Expression {
                    span: Span::new(start_pos, self.last_popped_end),
                    kind: ast::ExpressionKind::Path(path),
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
            _ => Err(Self::unexpected_token(self.peek(), EXPR_START_TOKENS, "expression"))
        }
    }

    fn path(&mut self) -> Result<ast::Path> {
        let mut parents = Vec::new();
        let mut id = self.identifier("identifier")?;

        while self.accept(TT::DoubleColon)?.is_some() {
            parents.push(id);
            id = self.identifier("path element")?;
        }

        Ok(ast::Path { span: Span::new(id.span.start, self.last_popped_end), parents, id })
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
            _ => Err(Self::unexpected_token(self.peek(), &[TT::Ampersand, TT::Id, TT::OpenB], "type declaration")),
        }
    }
}

pub fn parse_module(file: FileId, input: &str) -> Result<ast::Module> {
    let mut parser = Parser {
        tokenizer: Tokenizer::new(file, input)?,
        last_popped_end: Pos { file, line: 1, col: 1 },
    };
    parser.module()
}

use std::process::exit;

use crate::lexer::{LexedToken, Loc, Token, Tokens};

#[derive(Debug)]
pub enum Type {
    I32,
}

#[derive(Debug)]
pub enum Expr {
    IntLiteral(i32),
}

#[derive(Debug)]
pub enum Stmt {
    VarDecl {
        typ: Type,
        ident: String,
        expr: Expr,
    },
}

struct TokenReader<'a> {
    tokens: &'a [LexedToken],
    cur: usize,
    len: usize,
    eof: Loc,
}

impl<'a> TokenReader<'a> {
    fn new(t: &'a Tokens) -> Self {
        let tokens = t.get_tokens();
        Self {
            tokens: tokens,
            len: tokens.len(),
            cur: 0,
            eof: t.get_eof(),
        }
    }

    fn peek(&self) -> Option<&LexedToken> {
        if self.cur == self.len {
            return None;
        }
        Some(&self.tokens[self.cur])
    }

    fn next(&mut self) -> Option<&LexedToken> {
        if self.cur == self.len {
            return None;
        }
        self.cur += 1;
        Some(&self.tokens[self.cur - 1])
    }

    fn is_empty(&self) -> bool {
        self.cur == self.len
    }
}

/// Program AST
#[derive(Debug)]
pub struct ProgramTree {
    pub stmts: Vec<Stmt>,
}

/// Source code parser
pub struct Parser<'a> {
    reader: TokenReader<'a>,
    prog: ProgramTree,
}

impl<'a> Parser<'a> {
    pub fn new(t: &'a Tokens) -> Self {
        Parser {
            reader: TokenReader::new(t),
            prog: ProgramTree { stmts: Vec::new() },
        }
    }

    fn error(error: &str, loc: &Loc) {
        eprintln!("[ERR_PARSING] {}: {}", loc, error);
        exit(1);
    }

    fn handle_var_decl_stmt(&mut self) -> Stmt {
        // Read in the type
        let type_token = self.reader.next().unwrap();
        let decl_type = match type_token.token {
            Token::I32 => Type::I32,
            _ => panic!("type_token must be a valid type"),
        };

        // Read in the identifier
        let ident_token = match self.reader.next() {
            Some(t) => match &t.token {
                Token::Identifier(n) => n.clone(),
                _ => {
                    Self::error("expected identifier", &t.loc);
                    panic!();
                }
            },
            None => {
                Self::error("expected identifier", &self.reader.eof);
                panic!();
            }
        };

        // Read in equals sign
        match self.reader.next() {
            Some(t) => match t.token {
                Token::Equals => (),
                _ => {
                    Self::error("expected '='", &t.loc);
                }
            },
            None => {
                Self::error("expected identifier", &self.reader.eof);
            }
        }

        // Read in the expression
        // TODO move to seperate function to parse out full
        // non-literal expressions.
        let decl_expr = match self.reader.next() {
            Some(t) => match t.token {
                Token::IntLiteral(n) => Expr::IntLiteral(n.clone()),
                _ => {
                    Self::error("expected expression", &t.loc);
                    panic!();
                }
            },
            None => {
                Self::error("expected expression", &self.reader.eof);
                panic!();
            }
        };

        // Read in semicolon
        match self.reader.next() {
            Some(t) => match &t.token {
                Token::Semicolon => (),
                _ => {
                    Self::error("expected ';'", &t.loc);
                }
            },
            None => {
                Self::error("expected ';'", &self.reader.eof);
            }
        }

        Stmt::VarDecl {
            typ: decl_type,
            ident: ident_token,
            expr: decl_expr,
        }
    }

    pub fn parse(&mut self) -> &ProgramTree {
        while !self.reader.is_empty() {
            let token = match self.reader.peek() {
                Some(t) => t,
                None => break,
            };

            match token.token {
                Token::I32 => {
                    let stmt = self.handle_var_decl_stmt();
                    self.prog.stmts.push(stmt)
                }
                _ => break,
            }
        }
        &self.prog
    }
}

use crate::lexer::{Token, Tokens};

#[derive(Debug)]
pub struct SyntaxError {
    pub err_message: String,
}

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
    tokens: &'a [Token],
    cur: usize,
    len: usize,
}

impl<'a> TokenReader<'a> {
    fn new(t: &'a Tokens) -> Self {
        let tokens = t.get_tokens();
        Self {
            tokens: tokens,
            len: tokens.len(),
            cur: 0,
        }
    }

    fn peek(&self) -> Option<&Token> {
        if self.cur == self.len {
            return None;
        }
        Some(&self.tokens[self.cur])
    }

    fn next(&mut self) -> Option<&Token> {
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
    stmts: Vec<Stmt>,
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

    fn handle_var_decl_stmt(&mut self) -> Result<Stmt, SyntaxError> {
        // Read in the type
        let type_token = self.reader.next().unwrap();
        let decl_type = match type_token {
            Token::I32 => Type::I32,
            _ => panic!("type_token must be a valid type"),
        };

        // Read in the identifier
        let ident_token = match self.reader.next() {
            Some(t) => match t {
                Token::Identifier(n) => n.clone(),
                _ => {
                    return Err(SyntaxError {
                        err_message: format!("expected identifier"),
                    })
                }
            },
            None => {
                return Err(SyntaxError {
                    err_message: format!("expected identifier"),
                })
            }
        };

        // Read in equals sign
        match self.reader.next() {
            Some(t) => match t {
                Token::Equals => (),
                _ => {
                    return Err(SyntaxError {
                        err_message: format!("expected ="),
                    })
                }
            },
            None => {
                return Err(SyntaxError {
                    err_message: format!("expected ="),
                })
            }
        }

        // Read in the expression
        // TODO move to seperate function to parse out full
        // non-literal expressions.
        let decl_expr = match self.reader.next() {
            Some(t) => match t {
                Token::IntLiteral(n) => Expr::IntLiteral(n.clone()),
                _ => {
                    return Err(SyntaxError {
                        err_message: format!("expected expression"),
                    })
                }
            },
            None => {
                return Err(SyntaxError {
                    err_message: format!("expected expression"),
                })
            }
        };

        // Read in semicolon
        match self.reader.next() {
            Some(t) => match t {
                Token::Semicolon => (),
                _ => {
                    return Err(SyntaxError {
                        err_message: format!("expected ="),
                    })
                }
            },
            None => {
                return Err(SyntaxError {
                    err_message: format!("expected ="),
                })
            }
        }

        Ok(Stmt::VarDecl {
            typ: decl_type,
            ident: ident_token,
            expr: decl_expr,
        })
    }

    pub fn parse(&mut self) -> Result<&ProgramTree, SyntaxError> {
        while !self.reader.is_empty() {
            let token = match self.reader.peek() {
                Some(t) => t,
                None => break,
            };

            match token {
                Token::I32 => match self.handle_var_decl_stmt() {
                    Ok(stmt) => self.prog.stmts.push(stmt),
                    Err(e) => return Err(e),
                },
                _ => break,
            }
        }
        Ok(&self.prog)
    }
}

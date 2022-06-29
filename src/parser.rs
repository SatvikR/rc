use std::process::exit;

use crate::lexer::{LexedToken, Loc, Token, Tokens};

#[derive(Debug, Clone)]
pub enum Type {
    I32,
}

#[derive(Debug)]
pub enum BinOperator {
    Plus,
    Minus,
    Mult,
    Div,
    GreaterThan,
    LessThan,
    LogicalAnd,
    LogicalOr,
}

#[derive(Debug)]
pub enum Expr {
    IntLiteral(i32),
    BinOp {
        op: BinOperator,
        e1: Box<ParsedExpr>,
        e2: Box<ParsedExpr>,
    },
    Identifier(String),
}

#[derive(Debug)]
pub struct ParsedExpr {
    pub expr: Expr,
    pub loc: Loc,
}

#[derive(Debug)]
pub enum Stmt {
    VarDecl {
        typ: Type,
        ident: String,
        expr: ParsedExpr,
    },
    VarAsgmt {
        ident: String,
        expr: ParsedExpr,
    },
    Scope {
        stmts: Vec<ParsedStmt>,
    },
}

#[derive(Debug)]
pub struct ParsedStmt {
    pub stmt: Stmt,
    pub loc: Loc,
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
    pub stmts: Vec<ParsedStmt>,
}

/// Source code parser
pub struct Parser<'a> {
    reader: TokenReader<'a>,
    prog: ProgramTree,
    curr_stmt_loc: Option<Loc>,
}

impl<'a> Parser<'a> {
    pub fn new(t: &'a Tokens) -> Self {
        Parser {
            reader: TokenReader::new(t),
            prog: ProgramTree { stmts: Vec::new() },
            curr_stmt_loc: None,
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

        let decl_expr = self.handle_expression();

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

    fn handle_factor(&mut self) -> ParsedExpr {
        match self.reader.next() {
            Some(t) => match &t.token {
                Token::IntLiteral(n) => ParsedExpr {
                    expr: Expr::IntLiteral(*n),
                    loc: t.loc.clone(),
                },
                Token::OpenParan => {
                    let exp = self.handle_expression();
                    match self.reader.next() {
                        Some(t) => {
                            if !matches!(&t.token, Token::CloseParan) {
                                Self::error("expected ')'", &t.loc)
                            }
                            exp
                        }
                        None => {
                            Self::error("expected ')'", &self.reader.eof);
                            panic!();
                        }
                    }
                }
                Token::Identifier(s) => ParsedExpr {
                    expr: Expr::Identifier(String::from(s)),
                    loc: t.loc.clone(),
                },
                _ => {
                    Self::error("expected a ident, number or ( + expression + )", &t.loc);
                    panic!();
                }
            },
            None => {
                Self::error(
                    "expected a ident, number or ( + expression + )",
                    &self.reader.eof,
                );
                panic!();
            }
        }
    }

    fn handle_muldiv(&mut self) -> ParsedExpr {
        let mut exp = self.handle_factor();
        loop {
            // Read in *|/ operator if exists
            let exp_bin_op = match self.reader.peek() {
                Some(t) => match &t.token {
                    Token::Mult => BinOperator::Mult,
                    Token::Div => BinOperator::Div,
                    _ => return exp,
                },
                None => return exp,
            };
            self.reader.next();

            let exp_two = self.handle_factor();
            let loc = exp.loc.clone();
            exp = ParsedExpr {
                expr: Expr::BinOp {
                    op: exp_bin_op,
                    e1: Box::new(exp),
                    e2: Box::new(exp_two),
                },
                loc: loc,
            }
        }
    }

    fn handle_addsub(&mut self) -> ParsedExpr {
        let mut exp = self.handle_muldiv();
        loop {
            // Read in +|- operator if exists
            let exp_bin_op = match self.reader.peek() {
                Some(t) => match &t.token {
                    Token::Plus => BinOperator::Plus,
                    Token::Minus => BinOperator::Minus,
                    _ => return exp,
                },
                None => return exp,
            };
            self.reader.next();

            let exp_two = self.handle_muldiv();
            let loc = exp.loc.clone();
            exp = ParsedExpr {
                expr: Expr::BinOp {
                    op: exp_bin_op,
                    e1: Box::new(exp),
                    e2: Box::new(exp_two),
                },
                loc: loc,
            }
        }
    }

    fn handle_cmp(&mut self) -> ParsedExpr {
        let mut exp = self.handle_addsub();
        loop {
            // Read in <|> operator if exists
            let exp_bin_op = match self.reader.peek() {
                Some(t) => match &t.token {
                    Token::LessThan => BinOperator::LessThan,
                    Token::GreaterThan => BinOperator::GreaterThan,
                    _ => return exp,
                },
                None => return exp,
            };
            self.reader.next();

            let exp_two = self.handle_cmp();
            let loc = exp.loc.clone();
            exp = ParsedExpr {
                expr: Expr::BinOp {
                    op: exp_bin_op,
                    e1: Box::new(exp),
                    e2: Box::new(exp_two),
                },
                loc: loc,
            }
        }
    }

    fn handle_and(&mut self) -> ParsedExpr {
        let mut exp = self.handle_cmp();
        loop {
            // Read in && operator if exists
            match self.reader.peek() {
                Some(t) => {
                    if !matches!(&t.token, Token::LogicalAnd) {
                        return exp;
                    }
                }
                None => return exp,
            }
            self.reader.next();

            let exp_two = self.handle_cmp();
            let loc = exp.loc.clone();
            exp = ParsedExpr {
                expr: Expr::BinOp {
                    op: BinOperator::LogicalAnd,
                    e1: Box::new(exp),
                    e2: Box::new(exp_two),
                },
                loc: loc,
            }
        }
    }

    fn handle_or(&mut self) -> ParsedExpr {
        let mut exp = self.handle_and();
        loop {
            // Read in || operator if exists
            match self.reader.peek() {
                Some(t) => {
                    if !matches!(&t.token, Token::LogicalOr) {
                        return exp;
                    }
                }
                None => return exp,
            }
            self.reader.next();

            let exp_two = self.handle_and();
            let loc = exp.loc.clone();
            exp = ParsedExpr {
                expr: Expr::BinOp {
                    op: BinOperator::LogicalOr,
                    e1: Box::new(exp),
                    e2: Box::new(exp_two),
                },
                loc: loc,
            }
        }
    }

    /// Recursive descent parser for parsing expressions
    fn handle_expression(&mut self) -> ParsedExpr {
        self.handle_or()
    }

    fn handle_var_asgmt_stmt(&mut self) -> Stmt {
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
        let decl_expr = self.handle_expression();

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

        Stmt::VarAsgmt {
            ident: ident_token,
            expr: decl_expr,
        }
    }

    fn handle_scope(&mut self) -> Stmt {
        self.reader.next();
        let mut stmts = Vec::new();
        loop {
            let token = match self.reader.peek() {
                Some(t) => t,
                None => {
                    Self::error("expected a statement", &self.reader.eof);
                    panic!();
                }
            };

            if matches!(token.token, Token::CloseCurly) {
                self.reader.next();
                return Stmt::Scope { stmts: stmts };
            }

            let next_stmt = self.parse_stmt();
            stmts.push(next_stmt);
        }
    }

    fn parse_stmt(&mut self) -> ParsedStmt {
        let token = match self.reader.peek() {
            Some(t) => t,
            None => {
                Self::error("expected a statement", &self.reader.eof);
                panic!();
            }
        };
        self.curr_stmt_loc = Some(token.loc.clone());

        let stmt = match &token.token {
            Token::I32 => self.handle_var_decl_stmt(),
            Token::Identifier(_) => self.handle_var_asgmt_stmt(),
            Token::OpenCurly => self.handle_scope(),
            _ => {
                Self::error("invalid start to statement", &token.loc);
                panic!();
            }
        };
        ParsedStmt {
            stmt: stmt,
            loc: self.curr_stmt_loc.as_ref().unwrap().clone(),
        }
    }

    pub fn parse(&mut self) -> &ProgramTree {
        while !self.reader.is_empty() {
            let next_stmt = self.parse_stmt();
            self.prog.stmts.push(next_stmt);
        }
        &self.prog
    }
}

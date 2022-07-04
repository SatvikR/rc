use std::process::exit;

use crate::lexer::{LexedToken, Loc, Token, Tokens};

#[derive(Debug, Clone)]
pub enum Type {
    I32,
    I8,
    Array { typ: Box<Type>, size: u64 },
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
    RelationalEquals,
    RelationalNotEquals,
    LessThanOrEquals,
    GreaterThanOrEquals,
}

#[derive(Debug)]
pub enum UnaryOp {
    AddressOf,
}

#[derive(Debug)]
pub enum Expr {
    IntLiteral(u64),
    BinOp {
        op: BinOperator,
        e1: Box<ParsedExpr>,
        e2: Box<ParsedExpr>,
    },
    UnaryOp {
        op: UnaryOp,
        e: Box<ParsedExpr>,
    },
    Identifier(String),
    Call {
        ident: String,
        args: Vec<ParsedExpr>,
    },
    VarSubscript {
        ident: String,
        indices: Vec<ParsedExpr>,
    },
}

#[derive(Debug)]
pub struct ParsedExpr {
    pub expr: Expr,
    pub loc: Loc,
}

#[derive(Debug)]
/// Used in the function impl
pub struct Arg {
    pub typ: Type,
    pub ident: String,
}

#[derive(Debug)]
pub enum Stmt {
    VarDef {
        typ: Type,
        ident: String,
    },
    VarDecl {
        typ: Type,
        ident: String,
        expr: ParsedExpr,
    },
    VarAsgmt {
        ident: String,
        expr: ParsedExpr,
    },
    VarSubscriptAsgmt {
        ident: String,
        subscripts: Vec<ParsedExpr>,
        expr: ParsedExpr,
    },
    Scope {
        stmts: Vec<ParsedStmt>,
        args: Option<Vec<Arg>>,
    },
    IfStatement {
        cond: ParsedExpr,
        truthy: Box<ParsedStmt>,
        falsy: Option<Box<ParsedStmt>>,
    },
    WhileStatement {
        cond: ParsedExpr,
        body: Box<ParsedStmt>,
    },
    Function {
        ident: String,
        body: Box<ParsedStmt>, // args get passed in here
    },
    ReturnStatement {
        val: Option<ParsedExpr>,
    },
    AnonCall {
        ident: String,
        args: Vec<ParsedExpr>,
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

    fn token_to_type(t: &LexedToken) -> Type {
        match &t.token {
            Token::I32 => Type::I32,
            Token::I8 => Type::I8,
            _ => {
                Self::error("invalid type", &t.loc);
                panic!();
            }
        }
    }

    fn handle_array_size(&mut self) -> u64 {
        self.reader.next();
        let mut size = 1;
        loop {
            match self.reader.next() {
                Some(t) => match &t.token {
                    Token::IntLiteral(n) => size *= n,
                    _ => {
                        Self::error("cannot have dynamic array sizes", &t.loc);
                        panic!();
                    }
                },
                None => {
                    Self::error("expected array size", &self.reader.eof);
                    panic!();
                }
            }

            match self.reader.next() {
                Some(t) => {
                    if !matches!(&t.token, Token::CloseSquare) {
                        Self::error("expected ']'", &t.loc);
                    }
                }
                None => {
                    Self::error("expected ']'", &self.reader.eof);
                }
            }

            match self.reader.peek() {
                Some(t) => {
                    if !matches!(&t.token, Token::OpenSquare) {
                        break;
                    }
                    self.reader.next();
                }
                None => break,
            }
        }
        size
    }

    fn handle_var_decl_or_fn(&mut self) -> Stmt {
        // Read in the type
        let type_token = self.reader.next().unwrap();
        let base_type = Self::token_to_type(type_token);

        let decl_type = match self.reader.peek() {
            Some(t) => match &t.token {
                Token::OpenSquare => Type::Array {
                    typ: Box::new(base_type),
                    size: self.handle_array_size(),
                },
                _ => base_type,
            },
            None => {
                Self::error("expected var decl or fn", &self.reader.eof);
                panic!();
            }
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
        // Read in equals sign or open paran for a function
        match self.reader.next() {
            Some(t) => match t.token {
                Token::Semicolon => {
                    return Stmt::VarDef {
                        typ: decl_type,
                        ident: ident_token,
                    }
                }
                Token::Equals => (),
                Token::OpenParan => {
                    if matches!(decl_type, Type::Array { .. }) {
                        Self::error("cannot return array from a function", &t.loc);
                        panic!();
                    }
                    let mut args = Vec::new();
                    loop {
                        match self.reader.peek() {
                            Some(t) => {
                                if matches!(&t.token, Token::CloseParan) {
                                    break;
                                }
                            }
                            None => Self::error("expected ')'", &self.reader.eof),
                        }

                        if args.len() > 0 {
                            match self.reader.next() {
                                Some(t) => {
                                    if !matches!(&t.token, Token::Comma) {
                                        Self::error("expected ','", &t.loc);
                                    }
                                }
                                None => {
                                    Self::error("expected ','", &self.reader.eof);
                                }
                            }
                        }

                        // Read in the type
                        let decl_type = match self.reader.next() {
                            Some(t) => Self::token_to_type(t),
                            None => {
                                Self::error("expected a valid type", &self.reader.eof);
                                panic!();
                            }
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

                        args.push(Arg {
                            ident: ident_token,
                            typ: decl_type,
                        });
                    }

                    match self.reader.next() {
                        Some(t) => {
                            if !matches!(&t.token, Token::CloseParan) {
                                Self::error("expected ')'", &t.loc);
                            }
                        }
                        None => {
                            Self::error("expected ')'", &self.reader.eof);
                        }
                    }

                    match self.reader.peek() {
                        Some(t) => {
                            if !matches!(&t.token, Token::OpenCurly) {
                                Self::error("expected '{'", &t.loc);
                            }
                        }
                        None => {
                            Self::error("expected '{'", &self.reader.eof);
                        }
                    }

                    let scope_loc = self.reader.peek().unwrap().loc.clone();
                    let scope = self.handle_scope(Some(args));
                    return Stmt::Function {
                        ident: ident_token,
                        body: Box::new(ParsedStmt {
                            stmt: scope,
                            loc: scope_loc.clone(),
                        }),
                    };
                }
                _ => {
                    Self::error("expected '=' or '('", &t.loc);
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
                Token::Identifier(s) => {
                    let ident = String::from(s);
                    let loc = t.loc.clone();

                    match self.reader.peek() {
                        Some(t) => match &t.token {
                            Token::OpenParan => {
                                self.reader.next();
                                let mut args = Vec::new();
                                loop {
                                    match self.reader.peek() {
                                        Some(t) => {
                                            if matches!(&t.token, Token::CloseParan) {
                                                break;
                                            }
                                        }
                                        None => Self::error("expected ')'", &self.reader.eof),
                                    }

                                    if args.len() > 0 {
                                        match self.reader.next() {
                                            Some(t) => {
                                                if !matches!(&t.token, Token::Comma) {
                                                    Self::error("expected ','", &t.loc);
                                                }
                                            }
                                            None => {
                                                Self::error("expected ','", &self.reader.eof);
                                            }
                                        }
                                    }

                                    let arg = self.handle_expression();
                                    args.push(arg);
                                }
                                match self.reader.next() {
                                    Some(t) => match &t.token {
                                        Token::CloseParan => (),
                                        _ => {
                                            Self::error("expected ')'", &t.loc);
                                            panic!();
                                        }
                                    },
                                    None => {
                                        Self::error("expected ')'", &self.reader.eof);
                                        panic!();
                                    }
                                }

                                return ParsedExpr {
                                    expr: Expr::Call { ident, args },
                                    loc: loc.clone(),
                                };
                            }
                            Token::OpenSquare => {
                                // TODO nested indices
                                self.reader.next();
                                let mut subscripts = Vec::new();
                                loop {
                                    let idx = self.handle_expression();
                                    subscripts.push(idx);

                                    match self.reader.next() {
                                        Some(t) => {
                                            if !matches!(&t.token, Token::CloseSquare) {
                                                Self::error("expected ']'", &t.loc);
                                            }
                                        }
                                        None => {
                                            Self::error("expected ']'", &self.reader.eof);
                                        }
                                    }

                                    match self.reader.peek() {
                                        Some(t) => {
                                            if !matches!(&t.token, Token::OpenSquare) {
                                                break;
                                            }
                                            self.reader.next();
                                        }
                                        None => break,
                                    }
                                }

                                return ParsedExpr {
                                    expr: Expr::VarSubscript {
                                        ident,
                                        indices: subscripts,
                                    },
                                    loc: loc.clone(),
                                };
                            }
                            _ => (),
                        },
                        None => (),
                    }

                    ParsedExpr {
                        expr: Expr::Identifier(ident),
                        loc: loc.clone(),
                    }
                }
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

    fn handle_neg(&mut self) -> ParsedExpr {
        let loc;
        // Read in - if exists
        match self.reader.peek() {
            Some(t) => {
                if !matches!(&t.token, Token::Minus | Token::Ampersand) {
                    return self.handle_factor();
                }
                loc = t.loc.clone();
            }
            None => {
                Self::error(
                    "expected a ident, number or ( + expression + )",
                    &self.reader.eof,
                );
                panic!();
            }
        }
        let op = self.reader.next().unwrap().clone();

        let exp = self.handle_factor();

        let op_expr = match op.token {
            Token::Minus => Expr::BinOp {
                op: BinOperator::Minus,
                e1: Box::new(ParsedExpr {
                    expr: Expr::IntLiteral(0),
                    loc: loc.clone(),
                }),
                e2: Box::new(exp),
            },
            Token::Ampersand => Expr::UnaryOp {
                op: UnaryOp::AddressOf,
                e: Box::new(exp),
            },
            _ => panic!(),
        };

        ParsedExpr {
            expr: op_expr,
            loc: loc.clone(),
        }
    }

    fn handle_muldiv(&mut self) -> ParsedExpr {
        let mut exp = self.handle_neg();
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

            let exp_two = self.handle_neg();
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
                    Token::LessThanOrEquals => BinOperator::LessThanOrEquals,
                    Token::GreaterThanOrEquals => BinOperator::GreaterThanOrEquals,
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

    fn handle_rel(&mut self) -> ParsedExpr {
        let mut exp = self.handle_cmp();
        loop {
            // Read in ==|!= operator if exists
            let exp_bin_op = match self.reader.peek() {
                Some(t) => match &t.token {
                    Token::RelationalEquals => BinOperator::RelationalEquals,
                    Token::RelationalNotEquals => BinOperator::RelationalNotEquals,
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
        let mut exp = self.handle_rel();
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

            let exp_two = self.handle_rel();
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

    fn handle_var_asgmt_or_call(&mut self) -> Stmt {
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

        match self.reader.next() {
            Some(t) => match t.token {
                Token::Equals => (),
                Token::OpenSquare => {
                    let mut subscripts = Vec::new();
                    loop {
                        let idx = self.handle_expression();
                        subscripts.push(idx);

                        match self.reader.next() {
                            Some(t) => {
                                if !matches!(&t.token, Token::CloseSquare) {
                                    Self::error("expected ']'", &t.loc);
                                }
                            }
                            None => {
                                Self::error("expected ']'", &self.reader.eof);
                            }
                        }

                        match self.reader.peek() {
                            Some(t) => {
                                if !matches!(&t.token, Token::OpenSquare) {
                                    break;
                                }
                                self.reader.next();
                            }
                            None => break,
                        }
                    }

                    match self.reader.next() {
                        Some(t) => {
                            if !matches!(&t.token, Token::Equals) {
                                Self::error("expected '='", &t.loc);
                            }
                        }
                        None => {
                            Self::error("expected '='", &self.reader.eof);
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

                    return Stmt::VarSubscriptAsgmt {
                        ident: ident_token,
                        subscripts,
                        expr: decl_expr,
                    };
                }
                Token::OpenParan => {
                    let mut args = Vec::new();
                    loop {
                        match self.reader.peek() {
                            Some(t) => {
                                if matches!(&t.token, Token::CloseParan) {
                                    break;
                                }
                            }
                            None => Self::error("expected ')'", &self.reader.eof),
                        }

                        if args.len() > 0 {
                            match self.reader.next() {
                                Some(t) => {
                                    if !matches!(&t.token, Token::Comma) {
                                        Self::error("expected ','", &t.loc);
                                    }
                                }
                                None => {
                                    Self::error("expected ','", &self.reader.eof);
                                }
                            }
                        }

                        let arg = self.handle_expression();
                        args.push(arg);
                    }

                    match self.reader.next() {
                        Some(t) => match &t.token {
                            Token::CloseParan => (),
                            _ => {
                                Self::error("expected ')'", &t.loc);
                                panic!();
                            }
                        },
                        None => {
                            Self::error("expected ')'", &self.reader.eof);
                            panic!();
                        }
                    }

                    match self.reader.next() {
                        Some(t) => match &t.token {
                            Token::Semicolon => (),
                            _ => {
                                Self::error("expected ';'", &t.loc);
                                panic!();
                            }
                        },
                        None => {
                            Self::error("expected ';'", &self.reader.eof);
                            panic!();
                        }
                    }

                    return Stmt::AnonCall {
                        ident: ident_token,
                        args,
                    };
                }
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

    fn handle_scope(&mut self, args: Option<Vec<Arg>>) -> Stmt {
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
                return Stmt::Scope {
                    stmts: stmts,
                    args: if args.is_some() { args } else { None },
                };
            }

            let next_stmt = self.parse_stmt();
            stmts.push(next_stmt);
        }
    }

    fn handle_if(&mut self) -> Stmt {
        self.reader.next();
        match self.reader.next() {
            Some(t) => {
                if !matches!(&t.token, Token::OpenParan) {
                    Self::error("expected '('", &t.loc);
                    panic!();
                }
            }
            None => (),
        }

        let cond = self.handle_expression();

        match self.reader.next() {
            Some(t) => {
                if !matches!(&t.token, Token::CloseParan) {
                    Self::error("expected ')'", &t.loc);
                    panic!();
                }
            }
            None => (),
        }

        let truthy = self.parse_stmt();

        match self.reader.peek() {
            Some(t) => {
                if !matches!(&t.token, Token::Else) {
                    return Stmt::IfStatement {
                        cond: cond,
                        truthy: Box::new(truthy),
                        falsy: None,
                    };
                }
            }
            None => {
                return Stmt::IfStatement {
                    cond: cond,
                    truthy: Box::new(truthy),
                    falsy: None,
                };
            }
        }
        self.reader.next();
        let falsy = self.parse_stmt();

        Stmt::IfStatement {
            cond: cond,
            truthy: Box::new(truthy),
            falsy: Some(Box::new(falsy)),
        }
    }

    fn handle_while(&mut self) -> Stmt {
        self.reader.next();

        match self.reader.next() {
            Some(t) => {
                if !matches!(&t.token, Token::OpenParan) {
                    Self::error("expected '('", &t.loc);
                    panic!();
                }
            }
            None => (),
        }

        let cond = self.handle_expression();

        match self.reader.next() {
            Some(t) => {
                if !matches!(&t.token, Token::CloseParan) {
                    Self::error("expected ')'", &t.loc);
                    panic!();
                }
            }
            None => (),
        }

        let body = self.parse_stmt();
        Stmt::WhileStatement {
            cond: cond,
            body: Box::new(body),
        }
    }

    fn handle_return(&mut self) -> Stmt {
        self.reader.next();
        match self.reader.peek() {
            Some(t) => {
                if matches!(&t.token, Token::Semicolon) {
                    return Stmt::ReturnStatement { val: None };
                }
            }
            None => {
                Self::error("expected token(s) after return", &self.reader.eof);
                panic!();
            }
        }

        let val = self.handle_expression();
        match self.reader.next() {
            Some(t) => {
                if !matches!(&t.token, Token::Semicolon) {
                    Self::error("expected semicolon", &t.loc);
                }
            }
            None => {
                Self::error("expected semicolon", &self.reader.eof);
                panic!();
            }
        }

        Stmt::ReturnStatement { val: Some(val) }
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
            Token::I32 | Token::I8 => self.handle_var_decl_or_fn(),
            Token::Identifier(_) => self.handle_var_asgmt_or_call(),
            Token::OpenCurly => self.handle_scope(None),
            Token::If => self.handle_if(),
            Token::While => self.handle_while(),
            Token::Return => self.handle_return(),
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

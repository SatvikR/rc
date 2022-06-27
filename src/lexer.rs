use std::{fmt, process::exit};

#[derive(Debug)]
pub enum Token {
    IntLiteral(i32),
    Identifier(String),
    I32,
    Semicolon,
    Equals,
    Plus,
    Minus,
    Mult,
    Div,
    GreaterThan,
    LessThan,
    LogicalAnd,
}

#[derive(Debug)]
pub struct LexedToken {
    pub token: Token,
    pub loc: Loc,
}

/// Internal representation of source code
#[derive(Debug)]
pub struct Tokens {
    tokens: Vec<LexedToken>,
    eof: Option<Loc>,
}

impl Tokens {
    fn new() -> Self {
        Self {
            tokens: Vec::new(),
            eof: None,
        }
    }

    fn push(&mut self, t: LexedToken) {
        self.tokens.push(t);
    }

    pub fn get_tokens<'a>(&'a self) -> &'a [LexedToken] {
        self.tokens.as_slice()
    }

    pub fn get_eof(&self) -> Loc {
        self.eof.as_ref().unwrap().clone()
    }
}

pub struct SourceFile<'a> {
    path: String,
    data: &'a [u8],
}

impl<'a> SourceFile<'a> {
    pub fn new(path: String, data: &'a [u8]) -> Self {
        Self {
            path: path,
            data: data,
        }
    }

    pub fn get_root(&self) -> &str {
        let mut spl = self.path.split(".");
        return spl.next().unwrap();
    }
}

struct SourceCodeReader<'a> {
    src: &'a SourceFile<'a>,
    cur: usize,
    len: usize,
    loc: Loc,
}

impl<'a> SourceCodeReader<'a> {
    fn new(src_f: &'a SourceFile<'a>) -> Self {
        let src_len = src_f.data.len();
        let src_path = src_f.path.clone();

        return Self {
            src: src_f,
            len: src_len,
            cur: 0,
            loc: Loc {
                file: src_path,
                line: 1,
                col: 1,
            },
        };
    }

    fn get_loc(&self) -> Loc {
        Loc {
            file: self.loc.file.clone(),
            line: self.loc.line,
            col: self.loc.col,
        }
    }

    fn peek(&self) -> Option<char> {
        if self.cur == self.len {
            return None;
        }
        Some(self.src.data[self.cur] as char)
    }

    fn next(&mut self) -> Option<char> {
        if self.cur == self.len {
            return None;
        }
        if self.peek().unwrap() == '\n' {
            self.loc.line += 1;
            self.loc.col = 1
        } else {
            self.loc.col += 1;
        }

        self.cur += 1;
        Some(self.src.data[self.cur - 1] as char)
    }

    fn is_empty(&self) -> bool {
        self.cur == self.len
    }
}

#[derive(Debug, Clone)]
pub struct Loc {
    file: String,
    line: usize,
    col: usize,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

pub struct Lexer<'a> {
    token: String,
    reader: SourceCodeReader<'a>,
    tokens: Tokens,
    curr_token_loc: Option<Loc>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a SourceFile<'a>) -> Self {
        Self {
            token: String::from(""),
            reader: SourceCodeReader::new(src),
            tokens: Tokens::new(),
            curr_token_loc: None,
        }
    }

    fn error(&self, error: &str) {
        let loc = self.curr_token_loc.as_ref().unwrap();
        eprintln!("[ERR_LEXING] {}: {}", loc, error);
        exit(1);
    }

    fn push_token(&mut self, t: Token) {
        self.tokens.push(LexedToken {
            token: t,
            loc: self.curr_token_loc.as_ref().unwrap().clone(),
        });
    }

    fn is_seperator(token: char) -> bool {
        match token {
            ';' | '=' => true,
            _ => false,
        }
    }

    fn is_operator(token: char) -> bool {
        match token {
            '+' | '-' | '*' | '/' => true,
            _ => false,
        }
    }

    fn is_ascii_numeric(c: char) -> bool {
        '0' <= c && c <= '9'
    }

    fn handle_integer_literal(&mut self) -> Token {
        // TODO for floating points. This really should be its own
        // read function since it handles things like . differently
        self.read_word();

        match self.token.parse::<i32>() {
            Ok(n) => return Token::IntLiteral(n),
            Err(_) => {
                self.error("error reading int literal");
                panic!();
            }
        }
    }

    fn handle_literal(&mut self) -> Option<Token> {
        // is the token the beginning of a literal
        if Lexer::is_ascii_numeric(self.token.as_bytes()[0] as char) {
            return Some(self.handle_integer_literal());
        }
        None
    }

    /// Return a token if the source string is a seperator.
    fn handle_single_char(&self) -> Option<Token> {
        match self.token.as_str() {
            ";" => Some(Token::Semicolon),
            "=" => Some(Token::Equals),
            "+" => Some(Token::Plus),
            "-" => Some(Token::Minus),
            "*" => Some(Token::Mult),
            "/" => Some(Token::Div),
            ">" => Some(Token::GreaterThan),
            "<" => Some(Token::LessThan),
            _ => None,
        }
    }

    /// Handles operators that are more than one character.
    fn handle_special_operators(&mut self) -> Option<Token> {
        match self.token.as_str() {
            "&" => match self.reader.peek() {
                Some(c) => {
                    if c == '&' {
                        self.reader.next();
                        return Some(Token::LogicalAnd);
                    }
                    return None;
                }
                None => None,
            },
            _ => None,
        }
    }

    fn handle_keyword(&self) -> Option<Token> {
        match self.token.as_str() {
            "i32" => Some(Token::I32),
            _ => None,
        }
    }

    fn handle_word(&mut self) -> Option<Token> {
        self.read_word();

        match self.handle_keyword() {
            Some(t) => Some(t),
            None => Some(Token::Identifier(self.token.clone())),
        }
    }

    fn read_word(&mut self) {
        loop {
            match self.reader.peek() {
                Some(c) => {
                    if c == ' ' || Lexer::is_seperator(c) || Lexer::is_operator(c) {
                        return;
                    }
                    self.token.push(self.reader.next().unwrap());
                }
                None => {
                    self.error("error reading int literal");
                }
            }
        }
    }

    /// Performs lexical analysis on the source code
    pub fn lex(&mut self) -> &Tokens {
        while !self.reader.is_empty() {
            self.token = String::from("");
            self.curr_token_loc = Some(self.reader.get_loc());
            match self.reader.next() {
                Some(c) => self.token.push(c),
                None => break,
            }

            if self.token.as_bytes()[0].is_ascii_whitespace() {
                continue;
            }

            match self.handle_special_operators() {
                Some(t) => {
                    self.push_token(t);
                    continue;
                }
                None => (),
            }

            match self.handle_single_char() {
                Some(t) => {
                    self.push_token(t);
                    continue;
                }
                None => (),
            }

            match self.handle_literal() {
                Some(t) => {
                    self.push_token(t);
                    continue;
                }
                None => (),
            }

            match self.handle_word() {
                Some(t) => {
                    self.push_token(t);
                    continue;
                }
                None => {
                    self.error("invalid token");
                }
            }
        }
        self.tokens.eof = Some(self.reader.get_loc());
        &self.tokens
    }
}

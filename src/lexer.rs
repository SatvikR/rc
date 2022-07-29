use std::{fmt, fs::File, io::Read, process::exit};

#[derive(Debug, Clone)]
pub enum Token {
    IntLiteral(u64),
    StringLiteral(String),
    Identifier(String),
    If,
    Else,
    While,
    Return,
    Break,
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    Semicolon,
    Comma,
    Equals,
    Plus,
    Minus,
    Mult,
    Div,
    GreaterThan,
    LessThan,
    LogicalAnd,
    LogicalOr,
    OpenCurly,
    CloseCurly,
    OpenParan,
    CloseParan,
    OpenSquare,
    CloseSquare,
    RelationalEquals,
    RelationalNotEquals,
    LessThanOrEquals,
    GreaterThanOrEquals,
    Ampersand,
    Import,
    Arrow,
}

#[derive(Debug, Clone)]
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

pub fn load_src_file(path: &String) -> String {
    let mut src_f = match File::open(path) {
        Ok(f) => f,
        Err(_) => {
            eprintln!("err opening src file");
            exit(1);
        }
    };

    let mut src_str = String::new();
    match src_f.read_to_string(&mut src_str) {
        Ok(_) => (),
        Err(_) => {
            eprintln!("err reading src file");
            exit(1);
        }
    }

    return src_str;
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
        let len_path = self.path.len();
        let root = &self.path[0..len_path - 3];
        root
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
            ';' | '=' | '(' | ')' | ',' | '[' | ']' => true,
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

        match self.token.parse::<u64>() {
            Ok(n) => return Token::IntLiteral(n),
            Err(_) => {
                self.error("error reading int literal");
                panic!();
            }
        }
    }

    fn translate_escape(&self, c: char) -> char {
        match c {
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '0' => '\0',
            '\\' => '\\',
            _ => {
                self.error("unknown escape sequence");
                panic!();
            }
        }
    }

    fn handle_literal(&mut self) -> Option<Token> {
        // is the token the beginning of a literal
        if Lexer::is_ascii_numeric(self.token.as_bytes()[0] as char) {
            return Some(self.handle_integer_literal());
        }

        let token_str = self.token.as_str();
        match token_str {
            "'" => {
                let c = match self.reader.next() {
                    Some(c) => match c {
                        '\\' => match self.reader.next() {
                            Some(c) => match c {
                                '\'' => '\'',
                                _ => self.translate_escape(c),
                            },
                            None => {
                                self.error("expected escape sequence");
                                panic!();
                            }
                        },
                        _ => c,
                    },
                    None => {
                        self.error("expected a character literal");
                        panic!();
                    }
                };

                match self.reader.next() {
                    Some(c) => {
                        if c != '\'' {
                            self.error("missing closing quote in character literal");
                            panic!();
                        }
                    }
                    None => {
                        self.error("missing closing quote in character literal");
                    }
                }

                return Some(Token::IntLiteral(c as u64));
            }
            "\"" => {
                let mut buf = Vec::new();
                loop {
                    match self.reader.next() {
                        Some(c) => match c {
                            '\\' => match self.reader.next() {
                                Some(c) => match c {
                                    '"' => buf.push('"'),
                                    _ => buf.push(self.translate_escape(c)),
                                },
                                None => {
                                    self.error("expected escape sequence");
                                    panic!();
                                }
                            },
                            '"' => return Some(Token::StringLiteral(buf.into_iter().collect())),
                            _ => buf.push(c),
                        },
                        None => {
                            self.error("expected '\"'");
                            panic!();
                        }
                    }
                }
            }
            _ => return None,
        }
    }

    /// Return a token if the source string is a seperator.
    fn handle_single_char(&self) -> Option<Token> {
        match self.token.as_str().chars().nth(0).unwrap() {
            ';' => Some(Token::Semicolon),
            '=' => Some(Token::Equals),
            '+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '*' => Some(Token::Mult),
            '/' => Some(Token::Div),
            '>' => Some(Token::GreaterThan),
            '<' => Some(Token::LessThan),
            '{' => Some(Token::OpenCurly),
            '}' => Some(Token::CloseCurly),
            '(' => Some(Token::OpenParan),
            ')' => Some(Token::CloseParan),
            '[' => Some(Token::OpenSquare),
            ']' => Some(Token::CloseSquare),
            ',' => Some(Token::Comma),
            '&' => Some(Token::Ampersand),
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
            "|" => match self.reader.peek() {
                Some(c) => {
                    if c == '|' {
                        self.reader.next();
                        return Some(Token::LogicalOr);
                    }
                    return None;
                }
                None => None,
            },
            "=" => match self.reader.peek() {
                Some(c) => {
                    if c == '=' {
                        self.reader.next();
                        return Some(Token::RelationalEquals);
                    } else if c == '>' {
                        self.reader.next();
                        return Some(Token::Arrow);
                    }
                    return None;
                }
                None => None,
            },
            "!" => match self.reader.peek() {
                Some(c) => {
                    if c == '=' {
                        self.reader.next();
                        return Some(Token::RelationalNotEquals);
                    }
                    return None;
                }
                None => None,
            },
            "<" => match self.reader.peek() {
                Some(c) => {
                    if c == '=' {
                        self.reader.next();
                        return Some(Token::LessThanOrEquals);
                    }
                    return None;
                }
                None => None,
            },
            ">" => match self.reader.peek() {
                Some(c) => {
                    if c == '=' {
                        self.reader.next();
                        return Some(Token::GreaterThanOrEquals);
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
            "u8" => Some(Token::U8),
            "i8" => Some(Token::I8),
            "u16" => Some(Token::U16),
            "i16" => Some(Token::I16),
            "u32" => Some(Token::U32),
            "i32" => Some(Token::I32),
            "u64" | "ptr64" => Some(Token::U64),
            "i64" => Some(Token::I64),
            "if" => Some(Token::If),
            "else" => Some(Token::Else),
            "while" => Some(Token::While),
            "return" => Some(Token::Return),
            "break" => Some(Token::Break),
            "import" => Some(Token::Import),
            _ => None,
        }
    }

    fn handle_comment(&mut self) -> bool {
        match self.token.chars().nth(0) {
            Some(s) => match s {
                '/' => match self.reader.peek() {
                    Some(c) => match c {
                        '*' => {
                            // Keep reading bytes until a */
                            self.reader.next();

                            loop {
                                let next = match self.reader.next() {
                                    Some(c) => c,
                                    None => {
                                        self.error("exepcted '*/'");
                                        panic!();
                                    }
                                };

                                if next == '*' {
                                    match self.reader.peek() {
                                        Some(c) => match c {
                                            '/' => {
                                                self.reader.next();
                                                return true;
                                            }
                                            _ => (),
                                        },
                                        None => {
                                            self.error("exepcted '*/'");
                                            panic!();
                                        }
                                    }
                                }
                            }
                        }
                        _ => (),
                    },
                    None => (),
                },
                _ => (),
            },
            None => (),
        }
        false
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
                    if c == ' '
                        || Lexer::is_seperator(c)
                        || Lexer::is_operator(c)
                        || c.is_ascii_whitespace()
                    {
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

            if self.handle_comment() {
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

#[derive(Debug)]
pub enum Token {
    IntLiteral(i32),
    Identifier(String),
    I32,
    Semicolon,
    Equals,
}

/// Internal representation of source code
#[derive(Debug)]
pub struct Tokens {
    tokens: Vec<Token>,
}

impl Tokens {
    fn new() -> Self {
        Self { tokens: Vec::new() }
    }

    fn push(&mut self, t: Token) {
        self.tokens.push(t);
    }

    pub fn get_tokens<'a>(&'a self) -> &'a [Token] {
        self.tokens.as_slice()
    }
}

#[derive(Debug)]
pub struct ScanningError {
    pub err_message: String,
}

struct SourceCodeReader<'a> {
    src: &'a [u8],
    cur: usize,
    len: usize,
}

impl<'a> SourceCodeReader<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src: src.as_bytes(),
            len: src.len(),
            cur: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        if self.cur == self.len {
            return None;
        }
        Some(self.src[self.cur] as char)
    }

    fn next(&mut self) -> Option<char> {
        if self.cur == self.len {
            return None;
        }
        self.cur += 1;
        Some(self.src[self.cur - 1] as char)
    }

    fn is_empty(&self) -> bool {
        self.cur == self.len
    }
}

pub struct Lexer<'a> {
    token: String,
    reader: SourceCodeReader<'a>,
    tokens: Tokens,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            token: String::from(""),
            reader: SourceCodeReader::new(src),
            tokens: Tokens::new(),
        }
    }

    fn is_seperator(token: char) -> bool {
        match token {
            ';' | '=' => true,
            _ => false,
        }
    }

    fn is_ascii_numeric(c: char) -> bool {
        '0' <= c && c <= '9'
    }

    fn handle_integer_literal(&mut self) -> Result<Token, ScanningError> {
        // TODO for floating points. This really should be its own
        // read function since it handles things like . differently
        match self.read_word() {
            Ok(_) => (),
            Err(e) => return Err(e),
        }

        match self.token.parse::<i32>() {
            Ok(n) => return Ok(Token::IntLiteral(n)),
            Err(_) => {
                return Err(ScanningError {
                    err_message: format!("error reading int literal: {}", self.token,),
                })
            }
        }
    }

    fn handle_literal(&mut self) -> Option<Result<Token, ScanningError>> {
        // is the token the beginning of a literal
        if Lexer::is_ascii_numeric(self.token.as_bytes()[0] as char) {
            return Some(self.handle_integer_literal());
        }
        None
    }

    /// Return a token if the source string is a seperator.
    fn handle_seperator(&self) -> Option<Token> {
        match self.token.as_str() {
            ";" => Some(Token::Semicolon),
            "=" => Some(Token::Equals),
            _ => None,
        }
    }

    fn handle_keyword(&self) -> Option<Token> {
        match self.token.as_str() {
            "i32" => Some(Token::I32),
            _ => None,
        }
    }

    fn handle_word(&self) -> Option<Token> {
        match self.handle_keyword() {
            Some(t) => Some(t),
            None => Some(Token::Identifier(self.token.clone())),
        }
    }

    fn read_word(&mut self) -> Result<(), ScanningError> {
        loop {
            match self.reader.peek() {
                Some(c) => {
                    if c == ' ' || Lexer::is_seperator(c) {
                        return Ok(());
                    }
                    self.token.push(self.reader.next().unwrap());
                }
                None => {
                    return Err(ScanningError {
                        err_message: format!("invalid token {}", self.token),
                    })
                }
            }
        }
    }

    /// Performs lexical analysis on the source code
    pub fn lex(&mut self) -> Result<&Tokens, ScanningError> {
        while !self.reader.is_empty() {
            self.token = String::from("");
            match self.reader.next() {
                Some(c) => self.token.push(c),
                None => break,
            }

            if self.token.as_bytes()[0].is_ascii_whitespace() {
                continue;
            }

            let x = self.handle_literal();
            match x {
                Some(r) => match r {
                    Ok(t) => {
                        self.tokens.push(t);
                        continue;
                    }
                    Err(e) => return Err(e),
                },
                None => (),
            }

            match self.handle_seperator() {
                Some(t) => {
                    self.tokens.push(t);
                    continue;
                }
                None => (),
            }

            match self.read_word() {
                Ok(_) => (),
                Err(e) => return Err(e),
            }

            match self.handle_word() {
                Some(t) => {
                    self.tokens.push(t);
                    continue;
                }
                None => {
                    return Err(ScanningError {
                        err_message: format!("invalid token: {}", self.token),
                    })
                }
            }
        }
        Ok(&self.tokens)
    }
}

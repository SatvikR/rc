mod lexer;
mod parser;
use std::process::exit;

use lexer::Lexer;
use parser::Parser;

fn main() {
    let mut lexer = Lexer::new("i32 x = 10;");
    let tokens = match lexer.lex() {
        Ok(t) => t,
        Err(e) => {
            println!("{:?}", e.err_message);
            exit(1);
        }
    };

    let mut parser = Parser::new(tokens);
    let tree = match parser.parse() {
        Ok(tree) => tree,
        Err(e) => {
            println!("{:?}", e.err_message);
            exit(1);
        }
    };

    println!("{:?}", tree);
}

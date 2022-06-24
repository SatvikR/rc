mod codegen;
mod lexer;
mod parser;
use std::process::exit;

use lexer::Lexer;
use parser::Parser;

use crate::codegen::generate_x86_64;

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
    let parsed_program = match parser.parse() {
        Ok(tree) => tree,
        Err(e) => {
            println!("{:?}", e.err_message);
            exit(1);
        }
    };

    println!("{:?}", parsed_program);
    generate_x86_64(parsed_program).unwrap();
}

mod codegen;
mod lexer;
mod parser;
use std::{env, fs::File, io::Read, process::exit};

use lexer::Lexer;
use parser::Parser;

use crate::{codegen::generate_x86_64, lexer::SourceFile};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        println!("invalid command line arguments");
        exit(1);
    }

    let program_path = &args[1];

    let mut src_f = match File::open(program_path) {
        Ok(f) => f,
        Err(_) => {
            println!("err opening src file");
            exit(1);
        }
    };

    let mut src_str = String::new();
    match src_f.read_to_string(&mut src_str) {
        Ok(_) => (),
        Err(_) => {
            println!("err reading src file");
            exit(1);
        }
    }
    let src_buf = src_str.as_bytes();

    let src_file = SourceFile::new(program_path.to_string(), src_buf);

    let mut lexer = Lexer::new(src_file);
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

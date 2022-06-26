mod codegen;
mod lexer;
mod parser;
use std::{env, fs::File, io::Read, process::exit};

use codegen::generate_x86_64;
use lexer::Lexer;
use parser::Parser;

use crate::lexer::SourceFile;

fn load_src_file(path: &String) -> String {
    let mut src_f = match File::open(path) {
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

    return src_str;
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        println!("invalid command line arguments");
        exit(1);
    }

    let program_path = &args[1];
    let src_str = load_src_file(program_path);

    let src_buf = src_str.as_bytes();
    let src_file = SourceFile::new(program_path.to_string(), src_buf);

    let mut lexer = Lexer::new(src_file);
    let tokens = lexer.lex();

    let mut parser = Parser::new(tokens);
    let parsed_program = parser.parse();

    generate_x86_64(parsed_program).unwrap();
}

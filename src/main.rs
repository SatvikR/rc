mod codegen;
mod lexer;
mod parser;
use std::{
    env,
    io::{self, Write},
    process::{exit, Command},
};

use lexer::load_src_file;

use crate::{
    codegen::generate_x86_64,
    lexer::{Lexer, SourceFile},
    parser::Parser,
};

fn cmd_and_log(cmd: &str) {
    let output = Command::new("sh")
        .arg("-c")
        .arg(cmd)
        .output()
        .expect(&format!("[ERROR] Error running `{}`", cmd));

    println!("[CMD] {}", cmd);
    io::stdout().write_all(&output.stdout).unwrap();
    io::stderr().write_all(&output.stderr).unwrap();
    if !output.status.success() {
        exit(1);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("invalid command line arguments");
        exit(1);
    }

    let program_path = &args[1];
    let src_str = load_src_file(program_path);

    let src_buf = src_str.as_bytes();
    let src_file = &SourceFile::new(program_path.to_string(), src_buf);

    let mut lexer = Lexer::new(src_file);
    let tokens = lexer.lex();

    let mut parser = Parser::new(tokens);
    let parsed_program = parser.parse();

    let src_asm = format!("{}.asm", src_file.get_root());
    let src_obj = format!("{}.o", src_file.get_root());
    let src_exe = format!("{}", src_file.get_root());

    generate_x86_64(parsed_program, &src_asm).unwrap();

    cmd_and_log(&format!("nasm -felf64 {} -o {}", src_asm, src_obj));
    cmd_and_log(&format!("ld -o {} {}", src_exe, src_obj));
}

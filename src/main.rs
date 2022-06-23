use lexer::Lexer;
mod lexer;

fn main() {
    let mut lexer = Lexer::new("i32 x = 10;");
    match lexer.lex() {
        Ok(t) => {
            println!("{:?}", t);
        }
        Err(e) => {
            println!("{:?}", e.err_message);
        }
    }
}

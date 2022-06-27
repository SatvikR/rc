// Two stage code-gen
// 1. Convert AST to list of operations (Op for short)
// 2. Convert List of Op's to assembly output

use std::{
    collections::HashMap,
    fs::File,
    io::{BufWriter, Write},
};

use crate::parser::{BinOperator, Expr, ProgramTree, Stmt, Type};

#[derive(Debug)]
pub struct CompilerError {
    pub err_message: String,
}

/// High-level assembly instructions, a.k.a an intermediate representation
#[derive(Debug)]
enum Op {
    DefFn(String),
    PrepFn(i32),
    Push(i32),
    Pop,
    MovI32(i32), // value is the stack offset
    EndFn,
    Add,
    Sub,
    Mult,
    Div,
    Gt,
    Lt,
    JmpZero(String),
    Jmp(String),
    Lbl(String),
}

#[derive(Debug)]
struct IRProgram {
    ops: Vec<Op>,
}

struct IRSymbol {
    typ: Type,
    offset: i32,
}

// Stack Frame but more specifically a scope
struct IRFrame {
    symbols: HashMap<String, IRSymbol>,
}

struct IRFn {
    frames: Vec<IRFrame>, // stack of HashSets containing symbols
    prep_loc: usize,
    stack_size: i32,
}

impl IRFn {
    fn curr_frame(&mut self) -> &mut IRFrame {
        let pos = self.frames.len() - 1;
        return &mut self.frames[pos];
    }
}

struct IRGenCtx {
    curr_fn: Option<IRFn>,
    out: IRProgram,
    label: usize,
}

impl IRGenCtx {
    fn new() -> Self {
        Self {
            curr_fn: None,
            out: IRProgram { ops: Vec::new() },
            label: 0,
        }
    }

    fn get_curr_fn(&mut self) -> &mut IRFn {
        return self.curr_fn.as_mut().unwrap();
    }

    fn get_curr_frame(&mut self) -> &mut IRFrame {
        return self.get_curr_fn().curr_frame();
    }

    fn get_next_label(&mut self) -> String {
        self.label += 1;
        return String::from(format!(".L{}", self.label - 1));
    }
}

// Generates IR from an AST
struct IRGen<'a, 'b> {
    ast: &'a ProgramTree,
    ctx: &'b mut IRGenCtx,
}

impl<'a, 'b> IRGen<'a, 'b> {
    fn new(ast: &'a ProgramTree, ctx: &'b mut IRGenCtx) -> Self {
        Self { ast: ast, ctx: ctx }
    }

    fn introduce_function(&mut self, name: &str) {
        self.ctx.out.ops.push(Op::DefFn(name.to_string()));

        self.ctx.out.ops.push(Op::PrepFn(0));

        self.ctx.curr_fn = Some(IRFn {
            frames: Vec::new(),
            prep_loc: self.ctx.out.ops.len() - 1,
            stack_size: 0,
        });
        self.ctx.get_curr_fn().frames.push(IRFrame {
            symbols: HashMap::new(),
        });
    }

    fn end_function(&mut self) {
        self.ctx.out.ops.push(Op::EndFn);

        let prep_loc = self.ctx.get_curr_fn().prep_loc;

        match self.ctx.out.ops[prep_loc] {
            Op::PrepFn(_) => {
                self.ctx.out.ops[prep_loc] = Op::PrepFn(self.ctx.get_curr_fn().stack_size);
            }
            _ => panic!("Compiler Error: PrepFn Op was expected but not obtained"),
        }

        self.ctx.curr_fn = None;
    }

    fn gen_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::IntLiteral(n) => self.ctx.out.ops.push(Op::Push(*n)),
            Expr::BinOp { op, e1, e2 } => {
                // handle logical operators differently
                match op {
                    BinOperator::LogicalAnd => {
                        let lbl_false = self.ctx.get_next_label();
                        let lbl_out = self.ctx.get_next_label();

                        self.gen_expr(e1);
                        self.ctx.out.ops.push(Op::JmpZero(lbl_false.clone()));

                        self.gen_expr(e2);
                        self.ctx.out.ops.push(Op::JmpZero(lbl_false.clone()));

                        self.ctx.out.ops.push(Op::Push(1));
                        self.ctx.out.ops.push(Op::Jmp(lbl_out.clone()));

                        self.ctx.out.ops.push(Op::Lbl(lbl_false.clone()));
                        self.ctx.out.ops.push(Op::Push(0));

                        self.ctx.out.ops.push(Op::Lbl(lbl_out.clone()));
                        return;
                    }
                    _ => (),
                }

                self.gen_expr(e1);
                self.gen_expr(e2);
                match op {
                    BinOperator::Plus => self.ctx.out.ops.push(Op::Add),
                    BinOperator::Minus => self.ctx.out.ops.push(Op::Sub),
                    BinOperator::Mult => self.ctx.out.ops.push(Op::Mult),
                    BinOperator::Div => self.ctx.out.ops.push(Op::Div),
                    BinOperator::GreaterThan => self.ctx.out.ops.push(Op::Gt),
                    BinOperator::LessThan => self.ctx.out.ops.push(Op::Lt),
                    _ => panic!(),
                }
            }
        }
    }

    fn gen(&mut self) -> &IRProgram {
        self.introduce_function("main");
        for stmt in self.ast.stmts.iter() {
            match stmt {
                Stmt::VarDecl { typ, ident, expr } => {
                    assert!(
                        self.ctx.curr_fn.is_some(),
                        "cannot perform variable decl outside of function"
                    );

                    match typ {
                        Type::I32 => {
                            self.ctx.get_curr_fn().stack_size += 4;
                            let offset = self.ctx.get_curr_fn().stack_size;

                            self.gen_expr(expr);
                            self.ctx.out.ops.push(Op::Pop);
                            self.ctx.out.ops.push(Op::MovI32(offset));
                        }
                    }

                    let stack_size = self.ctx.get_curr_fn().stack_size;
                    self.ctx.get_curr_frame().symbols.insert(
                        ident.to_string(),
                        IRSymbol {
                            typ: Type::I32,
                            offset: stack_size,
                        },
                    );
                }
            }
        }
        self.end_function();
        return &self.ctx.out;
    }
}

pub fn generate_x86_64(ast: &ProgramTree, path: &str) -> std::io::Result<()> {
    let mut ctx = IRGenCtx::new();
    let mut ir_gen = IRGen::new(ast, &mut ctx);
    let program = ir_gen.gen();

    let f = File::create(path)?;
    let mut out = BufWriter::new(f);

    out.write_all(b"section .text\n")?;
    out.write_all(b"    global _start\n")?;
    out.write_all(b"_start:\n")?;
    out.write_all(b"    call main\n")?;
    out.write_all(b".debug_break:\n")?;
    out.write_all(b"    mov     rax, 60\n")?;
    out.write_all(b"    mov     rdi, 0\n")?;
    out.write_all(b"    syscall\n")?;

    for op in program.ops.iter() {
        match op {
            Op::DefFn(s) => {
                out.write_fmt(format_args!("{}:\n", s))?;
            }
            Op::PrepFn(i) => {
                out.write_fmt(format_args!("    push rbp\n"))?;
                out.write_fmt(format_args!("    mov rbp, rsp\n"))?;
                out.write_fmt(format_args!("    sub rsp, {}\n", i))?;
            }
            Op::Push(n) => {
                out.write_fmt(format_args!("    mov eax, {}\n", n))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Pop => {
                out.write_fmt(format_args!("    pop rax\n"))?;
            }
            Op::MovI32(i) => {
                out.write_fmt(format_args!("    mov DWORD [rbp-{}], eax\n", i))?;
            }
            Op::EndFn => {
                out.write_fmt(format_args!("    mov rsp, rbp\n"))?;
                out.write_fmt(format_args!("    pop rbp\n"))?;
                out.write_fmt(format_args!("    ret\n"))?;
            }
            Op::Add => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    add rax, rcx\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Sub => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    sub rax, rcx\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Mult => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    imul rax, rcx\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Div => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    mov edx, 0\n"))?;
                out.write_fmt(format_args!("    div rcx\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Gt => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, rcx\n"))?;
                out.write_fmt(format_args!("    setg al\n"))?;
                out.write_fmt(format_args!("    and al, 1\n"))?;
                out.write_fmt(format_args!("    movzx rax, al\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Lt => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, rcx\n"))?;
                out.write_fmt(format_args!("    setl al\n"))?;
                out.write_fmt(format_args!("    and al, 1\n"))?;
                out.write_fmt(format_args!("    movzx rax, al\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::JmpZero(l) => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, 0\n"))?;
                out.write_fmt(format_args!("    je {}\n", l))?;
            }
            Op::Jmp(l) => {
                out.write_fmt(format_args!("    jmp {}\n", l))?;
            }
            Op::Lbl(l) => {
                out.write_fmt(format_args!("{}:\n", l))?;
            }
        }
    }

    Ok(())
}

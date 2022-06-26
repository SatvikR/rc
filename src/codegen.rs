// Two stage code-gen
// 1. Convert AST to list of operations (Op for short)
// 2. Convert List of Op's to assembly output

use std::{collections::HashMap, fs::File, io::Write};

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
    Add,
    Sub,
    Pop,
    MovI32(i32), // value is the stack offset
    EndFn,
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
}

impl IRGenCtx {
    fn new() -> Self {
        Self {
            curr_fn: None,
            out: IRProgram { ops: Vec::new() },
        }
    }

    fn get_curr_fn(&mut self) -> &mut IRFn {
        return self.curr_fn.as_mut().unwrap();
    }

    fn get_curr_frame(&mut self) -> &mut IRFrame {
        return self.get_curr_fn().curr_frame();
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
                self.gen_expr(e1);
                self.gen_expr(e2);
                match op {
                    BinOperator::Plus => self.ctx.out.ops.push(Op::Add),
                    BinOperator::Minus => self.ctx.out.ops.push(Op::Sub),
                    _ => todo!(),
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

                    self.ctx.get_curr_fn().stack_size += 1;
                    let stack_size = self.ctx.get_curr_fn().stack_size;
                    self.ctx.get_curr_frame().symbols.insert(
                        ident.to_string(),
                        IRSymbol {
                            typ: Type::I32,
                            offset: stack_size,
                        },
                    );

                    match typ {
                        Type::I32 => {
                            let offset =
                                self.ctx.get_curr_frame().symbols.get(ident).unwrap().offset;

                            self.gen_expr(expr);
                            self.ctx.out.ops.push(Op::Pop);
                            self.ctx.out.ops.push(Op::MovI32(offset));
                        }
                    }
                }
            }
        }
        self.end_function();
        return &self.ctx.out;
    }
}

pub fn generate_x86_64(ast: &ProgramTree) -> std::io::Result<()> {
    let mut ctx = IRGenCtx::new();
    let mut ir_gen = IRGen::new(ast, &mut ctx);
    let program = ir_gen.gen();

    let mut out = File::create("./prog.asm")?;

    out.write_all(b"section .text\n")?;
    out.write_all(b"    global _start\n")?;
    out.write_all(b"_start:\n")?;
    out.write_all(b"    call main\n")?;
    out.write_all(b"    mov     rax, 60\n")?;
    out.write_all(b"    mov     rdi, 0\n")?;
    out.write_all(b"    syscall\n")?;

    for op in program.ops.iter() {
        match op {
            Op::DefFn(s) => out.write_fmt(format_args!("{}:\n", s))?,
            Op::PrepFn(i) => {
                out.write_fmt(format_args!("    push rbp\n"))?;
                out.write_fmt(format_args!("    mov rbp, rsp\n"))?;
                out.write_fmt(format_args!("    sub rsp, {}\n", i * 8))?;
            }
            Op::Push(n) => {
                out.write_fmt(format_args!("    mov eax, {}\n", n))?;
                out.write_fmt(format_args!("    push rax\n"))?;
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
            Op::Pop => {
                out.write_fmt(format_args!("    pop rax\n"))?;
            }
            Op::MovI32(i) => {
                out.write_fmt(format_args!("    mov DWORD [rbp-{}], eax\n", i * 8))?;
            }
            Op::EndFn => {
                out.write_fmt(format_args!("    mov rsp, rbp\n"))?;
                out.write_fmt(format_args!("    pop rbp\n"))?;
                out.write_fmt(format_args!("    ret\n"))?;
            }
        }
    }

    Ok(())
}

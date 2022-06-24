// Two stage code-gen
// 1. Convert AST to list of operations (Op for short)
// 2. Convert List of Op's to assembly output

use std::{collections::HashMap, fs::File, io::Write};

use crate::parser::{Expr, ProgramTree, Stmt, Type};

#[derive(Debug)]
pub struct CompilerError {
    pub err_message: String,
}

/// High-level assembly instructions, a.k.a an intermediate representation
#[derive(Debug)]
enum Op {
    DefFn(String),
    PrepFn(i32),
    MovI32 { offset: i32, val: i32 },
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
        self.ctx.curr_fn.as_mut().unwrap().frames.push(IRFrame {
            symbols: HashMap::new(),
        });
    }

    fn end_function(&mut self) {
        self.ctx.out.ops.push(Op::EndFn);

        match self.ctx.out.ops[self.ctx.curr_fn.as_mut().unwrap().prep_loc] {
            Op::PrepFn(_) => {
                self.ctx.out.ops[self.ctx.curr_fn.as_mut().unwrap().prep_loc] =
                    Op::PrepFn(self.ctx.curr_fn.as_mut().unwrap().stack_size)
            }
            _ => panic!("Compiler Error: PrepFn Op was expected but not obtained"),
        }

        self.ctx.curr_fn = None;
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

                    self.ctx.curr_fn.as_mut().unwrap().stack_size += 1;
                    self.ctx
                        .curr_fn
                        .as_mut()
                        .unwrap()
                        .curr_frame()
                        .symbols
                        .insert(
                            ident.to_string(),
                            IRSymbol {
                                typ: Type::I32,
                                offset: 1,
                            },
                        );

                    match typ {
                        Type::I32 => self.ctx.out.ops.push(Op::MovI32 {
                            offset: self
                                .ctx
                                .curr_fn
                                .as_mut()
                                .unwrap()
                                .curr_frame()
                                .symbols
                                .get(ident)
                                .unwrap()
                                .offset,
                            val: match expr {
                                Expr::IntLiteral(n) => *n,
                            },
                        }),
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
            Op::MovI32 { offset: i, val: n } => {
                out.write_fmt(format_args!("    mov DWORD [rbp-{}], {}\n", i * 8, n))?
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

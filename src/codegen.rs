// Two stage code-gen
// 1. Convert AST to list of operations (Op for short)
// 2. Convert List of Op's to assembly output

use core::panic;
use std::{
    collections::HashMap,
    fs::File,
    io::{BufWriter, Write},
    process::exit,
};

use crate::{
    lexer::Loc,
    parser::{BinOperator, Expr, ParsedExpr, ParsedStmt, ProgramTree, Stmt, Type, UnaryOp},
};

/// High-level assembly instructions, a.k.a an intermediate representation
#[derive(Debug)]
enum Op {
    DefFn(String),
    PrepFn(u64),
    /// pushing values
    Push(u64),
    PushArg(u64),
    PopArg,
    PushIdx(u64), // u64 is a size
    PushStr(u64), // u64 is a string index
    Lea(u64),
    /// value is the stack offset for the (Mov|Push)(8|16|32|64) Ops (for variables)
    Mov32(u64),
    Push32(u64),
    MovPtr32,
    PushPtr32,
    Mov8(u64),
    Push8(u64),
    MovPtr8,
    PushPtr8,
    EndFn,
    Add,
    Sub,
    Mult,
    Div,
    Gt,
    Lt,
    Leq,
    Geq,
    Eq,
    Neq,
    JmpZero(String),
    JmpNotZero(String),
    Jmp(String),
    Lbl(String),
    Call(String),
    PushCall,
    Ret,
}

#[derive(Debug)]
struct IRProgram {
    ops: Vec<Op>,
    strs: Vec<String>,
}

struct IRSymbol {
    typ: Type,
    offset: u64,
}

// Stack Frame but more specifically a scope
struct IRFrame {
    symbols: HashMap<String, IRSymbol>,
}

struct IRFn {
    frames: Vec<IRFrame>, // stack of HashSets containing symbols
    prep_loc: usize,
    stack_size: u64,
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
            out: IRProgram {
                ops: Vec::new(),
                strs: Vec::new(),
            },
            label: 0,
        }
    }

    fn get_curr_fn_mut(&mut self) -> &mut IRFn {
        return self.curr_fn.as_mut().unwrap();
    }

    fn get_curr_fn(&self) -> &IRFn {
        return self.curr_fn.as_ref().unwrap();
    }

    fn get_curr_frame(&mut self) -> &mut IRFrame {
        return self.get_curr_fn_mut().curr_frame();
    }

    fn get_next_label(&mut self) -> String {
        self.label += 1;
        return String::from(format!(".L{}", self.label - 1));
    }
}

// Generates IR from an AST
struct IRGen<'a> {
    ctx: &'a mut IRGenCtx,
}

impl<'a> IRGen<'a> {
    fn new(ctx: &'a mut IRGenCtx) -> Self {
        Self { ctx: ctx }
    }

    fn error(error: &str, loc: &Loc) {
        eprintln!("[ERR_CODEGEN] {}: {}", loc, error);
        exit(1);
    }

    fn register_string(&mut self, str: &String) -> u64 {
        self.ctx.out.strs.push(String::from(str));
        (self.ctx.out.strs.len() as u64) - 1
    }

    fn introduce_function(&mut self, name: &str) {
        self.ctx.out.ops.push(Op::DefFn(name.to_string()));

        self.ctx.out.ops.push(Op::PrepFn(0));

        self.ctx.curr_fn = Some(IRFn {
            frames: Vec::new(),
            prep_loc: self.ctx.out.ops.len() - 1,
            stack_size: 0,
        });
        self.ctx.get_curr_fn_mut().frames.push(IRFrame {
            symbols: HashMap::new(),
        });
    }

    fn end_function(&mut self) {
        self.ctx.out.ops.push(Op::EndFn);

        let prep_loc = self.ctx.get_curr_fn_mut().prep_loc;

        match self.ctx.out.ops[prep_loc] {
            Op::PrepFn(_) => {
                self.ctx.out.ops[prep_loc] = Op::PrepFn(self.ctx.get_curr_fn_mut().stack_size);
            }
            _ => panic!("Compiler Error: PrepFn Op was expected but not obtained"),
        }

        self.ctx.curr_fn = None;
    }

    fn gen_expr(&mut self, e: &ParsedExpr) {
        match &e.expr {
            Expr::IntLiteral(n) => self.ctx.out.ops.push(Op::Push(*n)),
            Expr::Identifier(ident) => {
                let symbol_opt = self.get_symbol(ident);
                match symbol_opt {
                    None => {
                        Self::error(&format!("undeclared identifier '{}'", ident), &e.loc);
                        panic!();
                    }
                    Some(_) => (),
                }

                let symbol = symbol_opt.unwrap();
                let typ = symbol.typ.clone();
                let offset = symbol.offset;
                self.gen_push(&typ, offset);
            }
            Expr::Call { ident, args } => {
                for arg in args.iter().rev() {
                    self.gen_expr(arg);
                }
                self.ctx.out.ops.push(Op::Call(String::from(ident)));
                for _ in 0..args.len() {
                    self.ctx.out.ops.push(Op::PopArg);
                }
                self.ctx.out.ops.push(Op::PushCall);
            }
            Expr::VarSubscript { ident, indices } => {
                // Push indeces onto stack in reverse order
                for idx in indices.iter().rev() {
                    self.gen_expr(idx);
                }

                // Put the address of the [0][0]...[0] element on the stack
                let sym = match self.get_symbol(ident) {
                    Some(s) => s,
                    None => {
                        Self::error("tried to dereference undeclared identifier", &e.loc);
                        panic!();
                    }
                };

                let offset = sym.offset;
                let mut curr_typ = sym.typ.clone();
                self.ctx.out.ops.push(Op::Lea(offset));

                // Do ptr math on each of the indices sequentially
                for _ in 0..indices.len() {
                    match &curr_typ {
                        Type::Array { typ, .. } => {
                            let inner_size = Self::get_size(&typ);
                            self.ctx.out.ops.push(Op::PushIdx(inner_size));
                            curr_typ = *typ.clone();
                        }
                        _ => Self::error("cannot subscript a non-array", &e.loc),
                    }
                }

                self.gen_push_ptr(&curr_typ);
            }
            Expr::AnonString(s) => {
                let str_idx = self.register_string(s);
                self.ctx.out.ops.push(Op::PushStr(str_idx));
            }
            Expr::UnaryOp { op, e } => match op {
                UnaryOp::AddressOf => {
                    let ident = match &e.expr {
                        Expr::Identifier(i) => i,
                        _ => {
                            Self::error("cannot take address of a non-variable", &e.loc);
                            panic!();
                        }
                    };

                    let sym = match self.get_symbol(ident) {
                        Some(s) => s,
                        None => {
                            Self::error("tried to dereference undeclared identifier", &e.loc);
                            panic!();
                        }
                    };

                    let offset = sym.offset;

                    self.ctx.out.ops.push(Op::Lea(offset));
                }
            },
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
                    BinOperator::LogicalOr => {
                        let lbl_true = self.ctx.get_next_label();
                        let lbl_out = self.ctx.get_next_label();

                        self.gen_expr(e1);
                        self.ctx.out.ops.push(Op::JmpNotZero(lbl_true.clone()));

                        self.gen_expr(e2);
                        self.ctx.out.ops.push(Op::JmpNotZero(lbl_true.clone()));

                        self.ctx.out.ops.push(Op::Push(0));
                        self.ctx.out.ops.push(Op::Jmp(lbl_out.clone()));

                        self.ctx.out.ops.push(Op::Lbl(lbl_true.clone()));
                        self.ctx.out.ops.push(Op::Push(1));

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
                    BinOperator::RelationalEquals => self.ctx.out.ops.push(Op::Eq),
                    BinOperator::RelationalNotEquals => self.ctx.out.ops.push(Op::Neq),
                    BinOperator::LessThanOrEquals => self.ctx.out.ops.push(Op::Leq),
                    BinOperator::GreaterThanOrEquals => self.ctx.out.ops.push(Op::Geq),
                    _ => panic!(),
                }
            }
        }
    }

    fn get_size(typ: &Type) -> u64 {
        match typ {
            Type::I32 => 4,
            Type::I8 => 1,
            Type::Array { typ, size } => *size * Self::get_size(typ),
        }
    }

    fn gen_mov(&mut self, typ: &Type, offset: u64) {
        match typ {
            Type::I32 => {
                self.ctx.out.ops.push(Op::Mov32(offset));
            }
            Type::I8 => {
                self.ctx.out.ops.push(Op::Mov8(offset));
            }
            Type::Array { typ, .. } => {
                self.gen_mov(typ, offset);
            }
        }
    }

    fn gen_mov_ptr(&mut self, typ: &Type) {
        match typ {
            Type::I32 => {
                self.ctx.out.ops.push(Op::MovPtr32);
            }
            Type::I8 => {
                self.ctx.out.ops.push(Op::MovPtr8);
            }
            Type::Array { typ, .. } => {
                self.gen_mov_ptr(typ);
            }
        }
    }

    fn gen_assign(&mut self, typ: &Type, val: &ParsedExpr, offset: u64) {
        self.gen_expr(val);
        self.gen_mov(typ, offset);
    }

    fn gen_push(&mut self, typ: &Type, offset: u64) {
        match typ {
            Type::I32 => {
                self.ctx.out.ops.push(Op::Push32(offset));
            }
            Type::I8 => {
                self.ctx.out.ops.push(Op::Push8(offset));
            }
            Type::Array { typ, .. } => {
                self.gen_push(typ, offset);
            }
        }
    }

    fn gen_push_ptr(&mut self, typ: &Type) {
        match typ {
            Type::I32 => {
                self.ctx.out.ops.push(Op::PushPtr32);
            }
            Type::I8 => {
                self.ctx.out.ops.push(Op::PushPtr8);
            }
            Type::Array { typ, .. } => {
                self.gen_push_ptr(typ);
            }
        }
    }

    fn get_symbol(&self, ident: &String) -> Option<&IRSymbol> {
        // Search backwards through the stackframes to look for a symbol
        for frame in self.ctx.get_curr_fn().frames.iter().rev() {
            match frame.symbols.get(ident) {
                Some(s) => return Some(s),
                _ => (),
            }
        }
        None
    }

    fn gen_str_init(&mut self, offset: u64, expr: &ParsedExpr) {
        self.gen_expr(expr);
        let str_idx = (self.ctx.out.strs.len() - 1) as u64;

        let raw_string = match &expr.expr {
            Expr::AnonString(s) => s,
            _ => panic!(),
        };

        for i in 0..raw_string.len() {
            self.ctx.out.ops.push(Op::PushPtr8);
            self.ctx.out.ops.push(Op::Mov8(offset - (i as u64)));

            self.ctx.out.ops.push(Op::PushStr(str_idx));
            self.ctx.out.ops.push(Op::Push(i as u64 + 1));
            self.ctx.out.ops.push(Op::Add);
        }

        self.ctx.out.ops.push(Op::PushPtr8);
        self.ctx
            .out
            .ops
            .push(Op::Mov8(offset - (raw_string.len() as u64)));
    }

    fn gen_stmt(&mut self, s: &ParsedStmt) {
        match &s.stmt {
            Stmt::VarDef { typ, ident } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot perform variable def outside of function"
                );

                self.ctx.get_curr_fn_mut().stack_size += Self::get_size(typ);
                let offset = self.ctx.get_curr_fn_mut().stack_size;

                self.ctx.get_curr_frame().symbols.insert(
                    ident.to_string(),
                    IRSymbol {
                        typ: typ.clone(),
                        offset: offset,
                    },
                );
            }
            Stmt::VarDecl { typ, ident, expr } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot perform variable decl outside of function"
                );

                self.ctx.get_curr_fn_mut().stack_size += Self::get_size(typ);
                let offset = self.ctx.get_curr_fn_mut().stack_size;

                self.ctx.get_curr_frame().symbols.insert(
                    ident.to_string(),
                    IRSymbol {
                        typ: typ.clone(),
                        offset: offset,
                    },
                );

                if (matches!(typ, Type::Array { .. }) && matches!(expr.expr, Expr::AnonString(_))) {
                    self.gen_str_init(offset, expr);
                } else {
                    self.gen_assign(&typ, expr, offset);
                }
            }
            Stmt::VarAsgmt { ident, expr } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot perform variable asgmt outside of function"
                );

                let symbol_option = self.get_symbol(ident);
                match symbol_option {
                    None => {
                        Self::error(&format!("undeclared identifier '{}'", ident), &s.loc);
                        panic!();
                    }
                    _ => (),
                };

                let symbol = symbol_option.unwrap();
                let typ = symbol.typ.clone();
                let offset = symbol.offset;

                if (matches!(typ, Type::Array { .. }) && matches!(expr.expr, Expr::AnonString(_))) {
                    self.gen_str_init(offset, expr);
                } else {
                    self.gen_assign(&typ, expr, offset);
                }
            }
            Stmt::VarSubscriptAsgmt {
                ident,
                subscripts,
                expr,
            } => {
                self.gen_expr(expr);

                for idx in subscripts.iter().rev() {
                    self.gen_expr(idx);
                }

                // Put the address of the [0][0]...[0] element on the stack
                let sym = match self.get_symbol(ident) {
                    Some(s) => s,
                    None => {
                        Self::error("tried to dereference undeclared identifier", &expr.loc);
                        panic!();
                    }
                };

                let offset = sym.offset;
                let mut curr_typ = sym.typ.clone();
                self.ctx.out.ops.push(Op::Lea(offset));

                // Do ptr math on each of the indices sequentially
                for _ in 0..subscripts.len() {
                    match &curr_typ {
                        Type::Array { typ, .. } => {
                            let inner_size = Self::get_size(&typ);
                            self.ctx.out.ops.push(Op::PushIdx(inner_size));
                            curr_typ = *typ.clone();
                        }
                        _ => Self::error("cannot subscript a non-array", &s.loc),
                    }
                }

                self.gen_mov_ptr(&curr_typ);
            }
            Stmt::Scope {
                stmts: scope_stmts,
                args,
            } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot have a scope outside a function"
                );
                self.ctx.get_curr_fn_mut().frames.push(IRFrame {
                    symbols: HashMap::new(),
                });

                // Check if this is the outermost stack of a function,
                // in which case, fetch all the arguments.
                if args.is_some() {
                    let args = args.as_ref().unwrap();
                    for (i, arg) in args.iter().enumerate() {
                        self.ctx.get_curr_fn_mut().stack_size += Self::get_size(&arg.typ);
                        let offset = self.ctx.get_curr_fn_mut().stack_size;

                        self.ctx.out.ops.push(Op::PushArg(16 + (i as u64) * 8));
                        self.gen_mov(&arg.typ, offset);

                        self.ctx.get_curr_frame().symbols.insert(
                            arg.ident.to_string(),
                            IRSymbol {
                                typ: arg.typ.clone(),
                                offset,
                            },
                        );
                    }
                }

                self.gen_stmts(scope_stmts);
                self.ctx.get_curr_fn_mut().frames.pop();
            }
            Stmt::AnonCall { ident, args } => {
                for arg in args.iter().rev() {
                    self.gen_expr(arg);
                }
                self.ctx.out.ops.push(Op::Call(String::from(ident)));
                for _ in 0..args.len() {
                    self.ctx.out.ops.push(Op::PopArg);
                }
            }
            Stmt::IfStatement {
                cond,
                truthy,
                falsy,
            } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot have an if statement outside a function"
                );
                let lbl_truthy = self.ctx.get_next_label();
                let lbl_falsy = self.ctx.get_next_label();
                let lbl_out = self.ctx.get_next_label();

                self.gen_expr(cond);
                self.ctx.out.ops.push(Op::JmpNotZero(lbl_truthy.clone()));
                self.ctx.out.ops.push(Op::Jmp(lbl_falsy.clone()));

                self.ctx.out.ops.push(Op::Lbl(lbl_truthy.clone()));
                self.gen_stmt(truthy);
                self.ctx.out.ops.push(Op::Jmp(lbl_out.clone()));

                self.ctx.out.ops.push(Op::Lbl(lbl_falsy.clone()));
                if falsy.is_some() {
                    self.gen_stmt(falsy.as_ref().unwrap());
                }

                self.ctx.out.ops.push(Op::Lbl(lbl_out.clone()));
            }
            Stmt::WhileStatement { cond, body } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot have a while statement outside a function"
                );
                let lbl_start = self.ctx.get_next_label();
                let lbl_out = self.ctx.get_next_label();

                self.ctx.out.ops.push(Op::Lbl(lbl_start.clone()));
                self.gen_expr(cond);
                self.ctx.out.ops.push(Op::JmpZero(lbl_out.clone()));

                self.gen_stmt(body);
                self.ctx.out.ops.push(Op::Jmp(lbl_start.clone()));

                self.ctx.out.ops.push(Op::Lbl(lbl_out.clone()));
            }
            Stmt::Function { ident, body } => {
                assert!(
                    self.ctx.curr_fn.is_none(),
                    "cannot define a function inside another function"
                );

                self.introduce_function(ident);
                self.gen_stmt(body);
                self.end_function();
            }
            Stmt::ReturnStatement { val } => {
                assert!(
                    self.ctx.curr_fn.is_some(),
                    "cannot return from outside a function"
                );
                match val {
                    Some(e) => self.gen_expr(e),
                    None => self.ctx.out.ops.push(Op::Push(0)),
                }

                self.ctx.out.ops.push(Op::Ret);
            }
        }
    }

    fn gen_stmts(&mut self, stmts: &Vec<ParsedStmt>) {
        for s in stmts.iter() {
            self.gen_stmt(s);
        }
    }

    fn gen_prog(&mut self, ast: &ProgramTree) -> &IRProgram {
        self.gen_stmts(&ast.stmts);

        &self.ctx.out
    }
}

pub fn generate_x86_64(ast: &ProgramTree, path: &str) -> std::io::Result<()> {
    let mut ctx = IRGenCtx::new();
    let mut ir_gen = IRGen::new(&mut ctx);
    let program = ir_gen.gen_prog(ast);

    let f = File::create(path)?;
    let mut out = BufWriter::new(f);

    out.write_all(b"section .data\n")?;

    for (i, s) in program.strs.iter().enumerate() {
        out.write_fmt(format_args!("    __str{}: db ", i))?;
        for b in s.as_bytes().iter() {
            out.write_fmt(format_args!("{},", b))?;
        }
        out.write_fmt(format_args!("0\n"))?; // Null terminator
    }

    out.write_all(b"section .text\n")?;
    out.write_all(b"    global _start\n")?;
    out.write_all(b"_start:\n")?;
    out.write_all(b"    call main\n")?;
    out.write_all(b".debug_break:\n")?;
    out.write_all(b"    mov     rdi, rax\n")?;
    out.write_all(b"    mov     rax, 60\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"; -- BEGIN SYSCALL INTRINSICS --\n")?;
    out.write_all(b"SYSCALL_0:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"SYSCALL_1:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    mov rdi, [rbp+24]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"SYSCALL_2:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    mov rdi, [rbp+24]\n")?;
    out.write_all(b"    mov rsi, [rbp+32]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"SYSCALL_3:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    mov rdi, [rbp+24]\n")?;
    out.write_all(b"    mov rsi, [rbp+32]\n")?;
    out.write_all(b"    mov rdx, [rbp+40]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"SYSCALL_4:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    mov rdi, [rbp+24]\n")?;
    out.write_all(b"    mov rsi, [rbp+32]\n")?;
    out.write_all(b"    mov rdx, [rbp+40]\n")?;
    out.write_all(b"    mov r10, [rbp+48]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"SYSCALL_5:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    mov rdi, [rbp+24]\n")?;
    out.write_all(b"    mov rsi, [rbp+32]\n")?;
    out.write_all(b"    mov rdx, [rbp+40]\n")?;
    out.write_all(b"    mov r10, [rbp+48]\n")?;
    out.write_all(b"    mov r8, [rbp+56]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"SYSCALL_6:\n")?;
    out.write_all(b"    push rbp\n")?;
    out.write_all(b"    mov rbp, rsp\n")?;
    out.write_all(b"    mov rax, [rbp+16]\n")?;
    out.write_all(b"    mov rdi, [rbp+24]\n")?;
    out.write_all(b"    mov rsi, [rbp+32]\n")?;
    out.write_all(b"    mov rdx, [rbp+40]\n")?;
    out.write_all(b"    mov r10, [rbp+48]\n")?;
    out.write_all(b"    mov r8, [rbp+56]\n")?;
    out.write_all(b"    mov r9, [rbp+64]\n")?;
    out.write_all(b"    syscall\n")?;
    out.write_all(b"    mov rsp, rbp\n")?;
    out.write_all(b"    pop rbp\n")?;
    out.write_all(b"    ret\n")?;
    out.write_all(b"; -- END SYSCALL INTRINSICS --\n")?;
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
            Op::EndFn => {
                out.write_fmt(format_args!(".LOUT:\n"))?;
                out.write_fmt(format_args!("    mov rsp, rbp\n"))?;
                out.write_fmt(format_args!("    pop rbp\n"))?;
                out.write_fmt(format_args!("    ret\n"))?;
            }
            Op::Push(n) => {
                out.write_fmt(format_args!("    mov rax, {}\n", n))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::PushArg(i) => {
                out.write_fmt(format_args!("    mov rax, QWORD [rbp+{}]\n", i))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::PopArg => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
            }
            Op::PushIdx(i) => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    imul rcx, {}\n", i))?;
                out.write_fmt(format_args!("    add rax, rcx\n"))?;
                out.write_fmt(format_args!("    lea rax, [rax]\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::PushStr(i) => {
                out.write_fmt(format_args!("    mov rax, __str{}\n", i))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Lea(i) => {
                out.write_fmt(format_args!("    lea rax, [rbp-{}]\n", i))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Mov32(i) => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    mov DWORD [rbp-{}], eax\n", i))?;
            }
            Op::Push32(i) => {
                out.write_fmt(format_args!("    mov rax, 0\n"))?;
                out.write_fmt(format_args!("    mov eax, DWORD [rbp-{}]\n", i))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::MovPtr32 => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    mov DWORD [rax], ecx\n"))?;
            }
            Op::PushPtr32 => {
                out.write_fmt(format_args!("    mov rax, 0\n"))?;
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    mov eax, DWORD [rcx]\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Mov8(i) => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    mov BYTE [rbp-{}], al\n", i))?;
            }
            Op::Push8(i) => {
                out.write_fmt(format_args!("    mov rax, 0\n"))?;
                out.write_fmt(format_args!("    mov al, BYTE [rbp-{}]\n", i))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::MovPtr8 => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    mov BYTE [rax], cl\n"))?;
            }
            Op::PushPtr8 => {
                out.write_fmt(format_args!("    mov rax, 0\n"))?;
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    mov al, BYTE [rcx]\n"))?;
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
            Op::Leq => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, rcx\n"))?;
                out.write_fmt(format_args!("    setle al\n"))?;
                out.write_fmt(format_args!("    and al, 1\n"))?;
                out.write_fmt(format_args!("    movzx rax, al\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Geq => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, rcx\n"))?;
                out.write_fmt(format_args!("    setge al\n"))?;
                out.write_fmt(format_args!("    and al, 1\n"))?;
                out.write_fmt(format_args!("    movzx rax, al\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Eq => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, rcx\n"))?;
                out.write_fmt(format_args!("    setz al\n"))?;
                out.write_fmt(format_args!("    and al, 1\n"))?;
                out.write_fmt(format_args!("    movzx rax, al\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Neq => {
                out.write_fmt(format_args!("    pop rcx\n"))?;
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, rcx\n"))?;
                out.write_fmt(format_args!("    setnz al\n"))?;
                out.write_fmt(format_args!("    and al, 1\n"))?;
                out.write_fmt(format_args!("    movzx rax, al\n"))?;
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::JmpZero(l) => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, 0\n"))?;
                out.write_fmt(format_args!("    jz {}\n", l))?;
            }
            Op::JmpNotZero(l) => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    cmp rax, 0\n"))?;
                out.write_fmt(format_args!("    jnz {}\n", l))?;
            }
            Op::Jmp(l) => {
                out.write_fmt(format_args!("    jmp {}\n", l))?;
            }
            Op::Lbl(l) => {
                out.write_fmt(format_args!("{}:\n", l))?;
            }
            Op::Call(l) => {
                out.write_fmt(format_args!("    call {}\n", l))?;
            }
            Op::PushCall => {
                out.write_fmt(format_args!("    push rax\n"))?;
            }
            Op::Ret => {
                out.write_fmt(format_args!("    pop rax\n"))?;
                out.write_fmt(format_args!("    jmp .LOUT\n"))?;
            }
        }
    }

    Ok(())
}

use crate::ast::*;
use crate::eval::*;
use std::collections::HashMap;
/// Translate the program

#[derive(Debug, Clone)]
pub struct Context {
    pub macros: HashMap<String, Macro>,
    variables: HashMap<String, Vec<Tok>>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            macros: HashMap::new(),
            variables: HashMap::new(),
        }
    }
    pub fn clean(&mut self) {
        self.variables.clear();
        self.macros.clear();
    }
}

pub fn eval_prog(prog: &Box<Prog>, context: &mut Box<Context>) {
    // Print the result of the program
    match &**prog {
        Prog::Stmts(stmt, p) => {
            // Add stmt to the context and evaluate remaining program
            eval_stmt(stmt.clone(), context);
            eval_prog(p, context);
        }
        Prog::Epsilon => {}
    }
}

fn eval_stmt(stmt: Stmt, context: &mut Box<Context>) {
    // Add a macro to the context
    // Context will be modified
    let ccon = context.clone();
    context.macros.insert(
        stmt.name.clone(),
        Macro {
            args: stmt.args.clone(),
            body: translate_tok(&stmt, &ccon),
        },
    );
}

fn translate_tok(stmt: &Stmt, context: &Box<Context>) -> Vec<Tok> {
    // Add para to context var
    let newcontext = &mut Box::new(*context.clone());
    for arg in &stmt.args {
        newcontext
            .variables
            .insert(arg.clone(), vec![Tok::Var(arg.clone())]);
    }
    trans_block(&stmt.block, newcontext)
}

fn compose_tok(toks: &Vec<Tok>) -> String {
    toks.iter()
        .map(|x| match x {
            Tok::Literal(y) => {
                if y.contains("\"") {
                    format!("`{}`", y)
                } else {
                    format!("\"{}\"", y)
                }
            }
            Tok::Var(y) => y.clone(),
        })
        .collect::<Vec<String>>()
        .join(" ")
}

fn trans_expr(expr: &Box<Expr>, context: &Box<Context>) -> Vec<Tok> {
    let tok: &mut Vec<Tok> = &mut Vec::new();
    match &**expr {
        Expr::Literal(x) => tok.push(Tok::Literal(x.clone())),
        Expr::Cat(x, y) => {
            tok.push(Tok::Var("cat".to_string()));
            tok.append(&mut trans_expr(x, context));
            tok.append(&mut trans_expr(y, context));
        }
        Expr::Var(x) => {
            let vartok = context.variables.get(x).expect("variable not in scope");
            tok.append(&mut vartok.clone())
        }
        Expr::MacAp(x) => {
            tok.push(Tok::Var(x.name.clone()));
            for a in &x.args {
                tok.append(&mut trans_expr(a, context));
            }
        }
        Expr::Block(x) => tok.append(&mut trans_block(x, &mut context.clone())),
        Expr::IExpr(x) => {
            tok.push(Tok::Var("!".to_string()));
            tok.append(&mut trans_expr(x, context));
        }
    }
    tok.to_vec()
}

fn trans_block(block: &Box<Block>, context: &mut Box<Context>) -> Vec<Tok> {
    // Translate one block to a list of tokens
    // let newcontext = &mut Box::new(*context.clone());
    let tok: &mut Vec<Tok> = &mut Vec::new();
    for bs in &block.bstmts {
        match &**bs {
            BStmt::VarDefine(name, expr) => {
                context
                    .variables
                    .insert(name.clone(), trans_expr(expr, context));
            }
            BStmt::MEq(lv, rv) => {
                tok.push(Tok::Var("let".to_string()));
                tok.append(&mut trans_expr(lv, context));
                tok.append(&mut trans_expr(rv, context));
            }
        }
    }
    tok.append(&mut trans_expr(&block.expr, context));
    tok.clone()
}

pub fn translate(prog: &Box<Prog>, context: &Box<Context>) -> String {
    match &**prog {
        Prog::Epsilon => "".to_string(),
        Prog::Stmts(x, y) => {
            let v = context.macros.get(x.name.as_str()).unwrap();
            let res = compose_tok(&v.body);
            let output = format!("{} {} = {}\n", x.name, x.args.join(" "), res);
            output + &translate(y, context)
        }
    }
}

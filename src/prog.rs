use std::collections::HashMap;

use crate::ast::*;

lalrpop_mod!(pub expr); // synthesized by LALRPOP
/// Evaluate Program

#[derive(Debug, Clone)]
struct Rule {
    // [y/x]z
    x: String,
    y: String,
}

#[derive(Debug, Clone)]
pub enum Symbol {
    Variable(String),
    Macro(Stmt),
    VarTok(Vec<Tok>),
}

#[derive(Debug, Clone)]
pub struct Context {
    symbols: HashMap<String, Symbol>,
    rules: Vec<Rule>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            symbols: HashMap::new(),
            rules: vec![],
        }
    }
}

pub fn eval_prog(prog: Box<Prog>, context: &mut Box<Context>) {
    // Print the result of the program
    match *prog {
        Prog::Stmts(stmt, p) => {
            // Add stmt to the context and evaluate remaining program
            eval_stmt(stmt, context);
            eval_prog(p, context);
        }
        Prog::Epsilon => {
            println!("no error found.");
        }
    }
}

pub fn eval_stmt(stmt: Stmt, context: &mut Box<Context>) {
    // Add a macro to the context
    // Context will be modified
    context
        .as_mut()
        .symbols
        .insert(stmt.name.clone(), Symbol::Macro(stmt));
}

fn apply_rule(x: &String, rules: &Vec<Rule>) -> String {
    // apply rules to a string
    let mut result = x.clone();
    for rule in rules.iter().rev() {
        if rule.x.is_empty() {
            panic!("empty rule detected");
        }
        result = result.replace(rule.x.as_str(), rule.y.as_str());
    }
    result
}

pub fn eval_macap(macap: &MacAp, context: &Box<Context>) -> String {
    let mut newcontext = *context.clone();
    // macro application
    newcontext = clear_context(&newcontext);
    let mac = context
        .symbols
        .get(&macap.name)
        .expect("macro not in scope");
    let mac = match mac {
        Symbol::Variable(_) => panic!("variable used as macro"),
        Symbol::Macro(x) => x,
        Symbol::VarTok(_) => panic!("variable token used as macro"),
    };
    // First evaluate arguments (by value)
    let args = macap
        .args
        .iter()
        .map(|x| eval_raw(x, context))
        .collect::<Vec<String>>();
    // add vars to the context
    for (result, name) in args.iter().zip(mac.args.iter()) {
        newcontext
            .symbols
            .insert(name.clone(), Symbol::Variable(result.clone()));
    }
    eval_block(&mac.block, &Box::new(newcontext))
}

fn clear_context(context: &Context) -> Context {
    // clear the context
    let mut newcontext = Context::new();
    newcontext.symbols = context
        .symbols
        .iter()
        .filter(|(_, v)| match v {
            Symbol::Variable(_) => false,
            Symbol::Macro(_) => true,
            Symbol::VarTok(_) => false,
        })
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    newcontext
}

fn clear_rules(context: &Context) -> Context {
    // clear the context
    let mut newcontext = Context::new();
    newcontext.symbols = context.symbols.clone();
    newcontext
}

pub fn eval_raw(expr: &Box<Expr>, context: &Box<Context>) -> String {
    // Evaluate an expression in a given context.
    // Will not apply rules
    match &**expr {
        Expr::Literal(x) => x.clone(),
        Expr::Cat(x, y) => eval_raw(x, context) + eval_raw(y, context).as_str(),
        Expr::Var(x) =>
        // use variables
        {
            let sym = context.symbols.get(x).expect("variable not in scope");
            match sym {
                Symbol::Variable(x) => x.clone(),
                Symbol::Macro(_) => panic!("macro used as variable"),
                Symbol::VarTok(_) => panic!("variable token used as variable"),
            }
        }
        Expr::MacAp(macap) => eval_macap(macap, context),
        Expr::Block(x) => eval_block(x, &Box::new(clear_rules(context))),
        Expr::IExpr(x) => {
            let res = eval_raw(x, context);
            let pres = &mut expr::ExpressionParser::new().parse(&res).unwrap();
            take_one_para(pres, &Box::new(clear_rules(context)))
        }
    }
}

pub fn eval(expr: &Box<Expr>, context: &Box<Context>) -> String {
    // Evaluate an expression in a given context.
    // Not allow to change context
    let res = eval_raw(expr, context);
    apply_rule(&res, &context.rules)
}

pub fn eval_block(block: &Box<Block>, context: &Box<Context>) -> String {
    // Context cannot be modified (local context)
    let lcontext = &mut Box::new(*context.clone());
    for bs in &block.bstmts {
        match &**bs {
            BStmt::VarDefine(name, expr) => {
                lcontext
                    .symbols
                    .insert(name.clone(), Symbol::Variable(eval_raw(expr, lcontext)));
            }
            BStmt::MEq(lv, rv) => {
                lcontext.rules.push(Rule {
                    x: eval_raw(lv, lcontext),
                    y: eval_raw(rv, lcontext),
                });
            }
        }
    }
    eval(&block.expr, lcontext)
}

pub fn take_one_para(expr: &mut Vec<Box<Tok>>, context: &Box<Context>) -> String {
    // Take one argument from the expression
    let first = eat_one_para(expr);
    match &*first {
        Tok::Literal(lit) => lit.clone(),
        Tok::Var(var) => {
            match var.as_str() {
                "let" => {
                    // Let expression
                    // let x y z = [y/x]z
                    let x = take_one_para(expr, context);
                    let y = take_one_para(expr, context);
                    let mut rules: Vec<Rule> = (*context.rules.clone()).to_vec();
                    rules.push(Rule { x, y });
                    let z = take_one_para(expr, context);
                    // Only here apply rule!
                    apply_rule(&z, &rules)
                }
                "cat" => {
                    // Concatenate expression
                    let cleancontext = &Box::new(clear_rules(context));
                    let x = take_one_para(expr, cleancontext);
                    let y = take_one_para(expr, cleancontext);
                    x + y.as_str()
                }
                "!" => {
                    // Eval expression
                    let exp = take_one_para(expr, context);
                    let pres = &mut expr::ExpressionParser::new().parse(&exp).unwrap();
                    take_one_para(pres, &Box::new(clear_rules(context)))
                }
                _ => {
                    let sym = context.symbols.get(var).expect("symbol not in scope");
                    match sym {
                        Symbol::Variable(y) => y.clone(),
                        Symbol::Macro(y) => {
                            // Apply macro here
                            let argnum = y.args.len();
                            let narg = take_paras(argnum, expr, &Box::new(clear_rules(context)));
                            let macap = MacAp {
                                name: var.clone(),
                                args: narg,
                            };
                            eval_macap(&macap, context)
                        }
                        Symbol::VarTok(_) => panic!("variable token used as variable"),
                    }
                }
            }
        }
    }
}

fn take_paras(n: usize, expr: &mut Vec<Box<Tok>>, context: &Box<Context>) -> Vec<Box<Expr>> {
    // Take n arguments from the expression
    (0..n)
        .map(|_| Box::new(Expr::Literal(take_one_para(expr, context))))
        .collect::<Vec<Box<Expr>>>()
}

fn eat_one_para(expr: &mut Vec<Box<Tok>>) -> Box<Tok> {
    // Take one argument from the expression
    let sd = expr.first().expect("missing argument").clone();
    expr.remove(0);
    sd
}

pub fn translate(stmt: Stmt, context: &Box<Context>) -> String {
    // Add para to context var
    let newcontext = &mut Box::new(*context.clone());
    for arg in &stmt.args {
        newcontext
            .symbols
            .insert(arg.clone(), Symbol::VarTok(vec![Tok::Var(arg.clone())]));
    }
    let toks = trans_block(&stmt.block, newcontext);
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
            let sym = context.symbols.get(x).expect("symbol not in scope");
            match sym {
                Symbol::VarTok(y) => tok.append(&mut y.clone()),
                _ => panic!("symbol not found"),
            }
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
                    .symbols
                    .insert(name.clone(), Symbol::VarTok(trans_expr(expr, context)));
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

pub fn trans_layout(context: &Box<Context>) {
    for (k, v) in &context.symbols {
        match v {
            Symbol::Macro(x) => {
                let args = x.args.join(",");
                let res = translate(x.clone(), context);
                println!("{}({}){{\n{}\n}}", k, args, res);
            }
            _ => {}
        }
    }
}

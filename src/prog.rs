use std::collections::HashMap;

use crate::ast::*;

lalrpop_mod!(pub expr); // synthesized by LALRPOP
/// Evaluate Program

#[derive(Debug, Clone)]
struct Rule {
    // [x/y]z
    x: String,
    y: String,
}

#[derive(Debug, Clone)]
pub enum Symbol {
    Variable(String),
    Macro(Stmt),
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
        if rule.y.is_empty() {
            panic!("empty rule detected");
        }
        result = result.replace(rule.y.as_str(), rule.x.as_str());
    }
    result
}

pub fn eval_macap(macap: &MacAp, context: &Box<Context>) -> String {
    let mut newcontext: Context = *context.clone();
    // macro application
    let mac = context
        .symbols
        .get(&macap.name)
        .expect("macro not in scope");
    let mac = match mac {
        Symbol::Variable(_) => panic!("variable used as macro"),
        Symbol::Macro(x) => x,
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
            }
        }
        Expr::MacAp(macap) => eval_macap(macap, context),
        Expr::Block(x) => eval_block(x, context),
        Expr::IExpr(x) => {
            let res = eval_raw(x, context);
            let pres = &mut expr::ExpressionParser::new().parse(&res).unwrap();
            take_one_para(pres, context)
        }
    }
}

pub fn eval(expr: &Box<Expr>, context: &Box<Context>) -> String {
    // Evaluate an expression in a given context.
    // Not allow to change context
    match &**expr {
        Expr::Literal(x) => apply_rule(x, &context.rules),
        Expr::Cat(x, y) => {
            let cat = eval_raw(x, context) + eval_raw(y, context).as_str();
            apply_rule(&cat, &context.rules)
        }
        _ =>
        // other cases
        {
            let res = eval_raw(expr, context);
            apply_rule(&res, &context.rules)
        }
    }
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
                    x: eval_raw(rv, lcontext),
                    y: eval_raw(lv, lcontext),
                });
            }
        }
    }
    eval(&block.expr, lcontext)
}

fn take_one_para(expr: &mut Vec<Box<Tok>>, context: &Box<Context>) -> String {
    // Take one argument from the expression
    let first = eat_one_para(expr);
    match &*first {
        Tok::Literal(x) => x.clone(),
        Tok::Var(x) => {
            let sym = context.symbols.get(x).expect("symbol not in scope");
            match sym {
                Symbol::Variable(y) => y.clone(),
                Symbol::Macro(y) => {
                    // Apply macro here
                    let argnum = y.args.len();
                    let narg = take_paras(argnum, expr, context);
                    let macap = MacAp {
                        name: x.clone(),
                        args: narg,
                    };
                    eval_macap(&macap, context)
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

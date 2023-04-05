use std::collections::HashMap;

use crate::ast::Tok;
use crate::eval::*;

// lazycat Evaluater

#[derive(Debug, Clone)]
struct Rule {
    // [y/x]z
    x: String,
    y: Vec<Tok>,
}

#[derive(Debug, Clone)]
pub enum Symbol {
    Variable(Vec<Tok>),
    Macro(Macro),
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
            rules: Vec::new(),
        }
    }
}
fn eval_macap(mac: &Macro, args: &Vec<Vec<Tok>>, context: &Box<Context>) -> String {
    let mut newcontext = *context.clone();
    // add vars to the context
    for (result, name) in args.iter().zip(mac.args.iter()) {
        newcontext
            .symbols
            .insert(name.clone(), Symbol::Variable(result.clone()));
    }
    let block = &mut mac.body.clone();
    eval_strict(block, &Box::new(newcontext))
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

fn apply_rule(x: &String, rules: &Vec<Rule>, context: &Box<Context>) -> String {
    // apply rules to a string
    let mut result = x.clone();
    for rule in rules.iter().rev() {
        if rule.x.is_empty() {
            panic!("empty rule detected");
        }
        if result.contains(rule.x.as_str()) {
            result = result.replace(rule.x.as_str(), &eval_strict(&mut rule.y.clone(), context));
        }
    }
    result
}

fn eval_strict(expr: &mut Vec<Tok>, context: &Box<Context>) -> String {
    // Take one argument from the expression
    let first = eat_one_para(expr);
    match &first {
        Tok::Literal(lit) => lit.clone(),
        Tok::Var(var) => {
            match var.as_str() {
                "let" => {
                    // Let expression
                    // let x y z = [y/x]z
                    let x = eval_strict(expr, context);
                    let y = eval_lazy(expr, context);
                    let mut rules: Vec<Rule> = (*context.rules.clone()).to_vec();
                    rules.push(Rule { x, y });
                    let z = eval_strict(expr, context);
                    // Only here apply rule!
                    apply_rule(&z, &rules, context)
                }
                "cat" => {
                    // Concatenate expression
                    let cleancontext = &Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    let y = eval_strict(expr, cleancontext);
                    x + y.as_str()
                }
                _ => {
                    let sym = context
                        .symbols
                        .get(var)
                        .expect(format!("symbol {} not in scope", var).as_str());
                    match &sym {
                        Symbol::Variable(y) => {
                            eval_strict(&mut y.clone(), &Box::new(clear_rules(context)))
                        }
                        Symbol::Macro(y) => {
                            // Apply macro here
                            let argnum = y.args.len();
                            let narg =
                                take_paras_lazy(argnum, expr, &Box::new(clear_rules(context)));
                            eval_macap(y, &narg, &Box::new(clear_context(context)))
                        }
                    }
                }
            }
        }
    }
}

fn eval_lazy(expr: &mut Vec<Tok>, context: &Box<Context>) -> Vec<Tok> {
    // Take one argument from the expression
    let first = eat_one_para(expr);
    match &first {
        Tok::Literal(lit) => vec![Tok::Literal(lit.clone())],
        Tok::Var(var) => {
            match var.as_str() {
                "let" => {
                    // Let expression
                    // let x y z = [y/x]z
                    let x = eval_lazy(expr, context);
                    let y = eval_lazy(expr, context);
                    let z = eval_lazy(expr, context);
                    [vec![first], x, y, z].concat()
                }
                "cat" => {
                    // Concatenate expression
                    // let cleancontext = &Box::new(clear_rules(context));
                    let x = eval_lazy(expr, context);
                    let y = eval_lazy(expr, context);
                    [vec![first], x, y].concat()
                }
                _ => {
                    let sym = context
                        .symbols
                        .get(var)
                        .expect(format!("symbol {} not in scope", var).as_str());
                    match &sym {
                        Symbol::Variable(y) => y.clone(),
                        Symbol::Macro(y) => {
                            // Apply macro here
                            let argnum = y.args.len();
                            let narg = take_paras_lazy(argnum, expr, context);
                            [vec![first], narg.concat()].concat()
                        }
                    }
                }
            }
        }
    }
}

fn take_paras_lazy(n: usize, expr: &mut Vec<Tok>, context: &Box<Context>) -> Vec<Vec<Tok>> {
    // Take n arguments from the expression
    (0..n)
        .map(|_| eval_lazy(expr, context))
        .collect::<Vec<Vec<Tok>>>()
}

fn eat_one_para(expr: &mut Vec<Tok>) -> Tok {
    // Take one argument from the expression
    let sd = expr.first().expect("missing argument").clone();
    expr.remove(0);
    sd
}

pub fn eval(macros: &HashMap<String, Macro>, expr: &Vec<Tok>) -> String {
    // Evaluate the expression
    let mut context = Context::new();
    for (k, v) in macros.iter() {
        context.symbols.insert(k.clone(), Symbol::Macro(v.clone()));
    }
    let exp = &mut expr.clone();
    eval_strict(exp, &Box::new(context))
}

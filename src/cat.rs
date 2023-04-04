use std::collections::HashMap;

use crate::ast::Tok;
use crate::eval::*;

// Cat Evaluater
// Given a cat expression, evaluate it to a string
// Also given a context

lalrpop_mod!(pub expr);

#[derive(Debug, Clone)]
struct Rule {
    // [y/x]z
    x: String,
    y: String,
}

#[derive(Debug, Clone)]
pub enum Symbol {
    Variable(String),
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
fn eval_macap(mac: &Macro, args: &Vec<String>, context: &Box<Context>) -> String {
    let mut newcontext = *context.clone();
    // add vars to the context
    for (result, name) in args.iter().zip(mac.args.iter()) {
        newcontext
            .symbols
            .insert(name.clone(), Symbol::Variable(result.clone()));
    }
    let block = &mut mac.body.clone();
    take_one_para(block, &Box::new(newcontext))
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

fn take_one_para(expr: &mut Vec<Tok>, context: &Box<Context>) -> String {
    // Take one argument from the expression
    let first = eat_one_para(expr);
    match &first {
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
                    let sym = context
                        .symbols
                        .get(var)
                        .expect(format!("symbol {} not in scope", var).as_str());
                    match &sym {
                        Symbol::Variable(y) => y.clone(),
                        Symbol::Macro(y) => {
                            // Apply macro here
                            let argnum = y.args.len();
                            let narg = take_paras(argnum, expr, &Box::new(clear_rules(context)));
                            eval_macap(y, &narg, &Box::new(clear_context(context)))
                        }
                    }
                }
            }
        }
    }
}

fn take_paras(n: usize, expr: &mut Vec<Tok>, context: &Box<Context>) -> Vec<String> {
    // Take n arguments from the expression
    (0..n)
        .map(|_| take_one_para(expr, context))
        .collect::<Vec<String>>()
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
    take_one_para(exp, &Box::new(context))
}

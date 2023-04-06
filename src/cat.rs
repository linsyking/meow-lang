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
    libsyms: HashMap<String, usize>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            symbols: HashMap::new(),
            rules: Vec::new(),
            libsyms: HashMap::from(
                [
                    ("cat", 2),
                    ("let", 3),
                    ("hd", 1),
                    ("tl", 1),
                    ("if", 3),
                    ("eq", 2),
                    ("len", 1),
                    ("num", 1),
                    ("show", 1),
                ]
                .map(|(k, v)| (k.to_string(), v)),
            ),
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
    eval_strict(block, &mut Box::new(newcontext))
}

fn clear_context(context: &Context) -> Context {
    // clear the context
    let mut newcontext = context.clone();
    newcontext.symbols = newcontext
        .symbols
        .iter()
        .filter(|(_, v)| match v {
            Symbol::Variable(_) => false,
            Symbol::Macro(_) => true,
        })
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    newcontext.rules.clear();
    newcontext
}

fn clear_rules(context: &Context) -> Context {
    // clear the context
    let mut newcontext = context.clone();
    newcontext.rules.clear();
    newcontext
}

fn apply_rule(x: &String, rules: &Vec<Rule>, context: &mut Box<Context>) -> String {
    // apply rules to a string
    let mut result = x.clone();
    for rule in rules.iter().rev() {
        if rule.x.is_empty() {
            panic!("empty rule detected");
        }
        if result.contains(rule.x.as_str()) {
            let varres = eval_strict(&mut rule.y.clone(), context);
            result = result.replace(rule.x.as_str(), &varres);
        }
    }
    result
}

fn num_to_s(num: usize) -> String {
    let mut result = String::new();
    for _ in 0..num {
        result.push('S');
    }
    result.push('0');
    result
}

fn s_to_num(s: &String) -> usize {
    s.chars().filter(|c| *c == 'S').count()
}

fn eval_strict(expr: &mut Vec<Tok>, context: &mut Box<Context>) -> String {
    // Take one argument from the expression
    // println!("[strict] {:?}", expr);
    let first = eat_one_para(expr);
    match &first {
        Tok::Literal(lit) => lit.clone(),
        Tok::Var(var) => {
            match var.as_str() {
                "let" => {
                    // Let expression
                    // let x y z = [y/x]z
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    let y = eval_lazy(expr, cleancontext);
                    // println!("let lazy: {:?}", y);
                    let mut rules: Vec<Rule> = (*context.rules.clone()).to_vec();
                    rules.push(Rule { x, y });
                    let z = eval_strict(expr, cleancontext);
                    // Only here apply rule!
                    apply_rule(&z, &rules, context)
                }
                "cat" => {
                    // Concatenate expression
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    let y = eval_strict(expr, cleancontext);
                    x + y.as_str()
                }
                "hd" => {
                    // Head of a string
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    if x.is_empty() {
                        String::new()
                    } else {
                        x.chars().next().unwrap().to_string()
                    }
                }
                "tl" => {
                    // Tail of a string
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    if x.is_empty() {
                        String::new()
                    } else {
                        x.chars().skip(1).collect()
                    }
                }
                "if" => {
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    let y = &mut eval_lazy(expr, cleancontext);
                    let z = &mut eval_lazy(expr, cleancontext);
                    if &x == "T" {
                        eval_strict(y, cleancontext)
                    } else {
                        eval_strict(z, cleancontext)
                    }
                }
                "eq" => {
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    let y = eval_strict(expr, cleancontext);
                    if x == y {
                        "T".to_string()
                    } else {
                        "F".to_string()
                    }
                }
                "len" => {
                    // Length of a string
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    num_to_s(x.len())
                }
                "num" => {
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    let rn: usize = x.parse().unwrap();
                    num_to_s(rn)
                }
                "show" => {
                    let cleancontext = &mut Box::new(clear_rules(context));
                    let x = eval_strict(expr, cleancontext);
                    s_to_num(&x).to_string()
                }
                _ => {
                    let sym = context
                        .symbols
                        .get(var)
                        .expect(format!("symbol {} not in scope", var).as_str());
                    match &sym {
                        Symbol::Variable(y) => {
                            eval_strict(&mut y.clone(), &mut Box::new(clear_rules(context)))
                        }
                        Symbol::Macro(y) => {
                            // Apply macro here
                            let argnum = y.args.len();
                            let narg =
                                take_paras_lazy(argnum, expr, &Box::new(clear_rules(context)));
                            // println!("macro args: {:?}", narg);
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
            if context.libsyms.contains_key(var.as_str()) {
                // Library symbols
                let narg =
                    take_paras_lazy(*context.libsyms.get(var.as_str()).unwrap(), expr, context);
                [vec![first], narg.concat()].concat()
            } else {
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
    eval_strict(exp, &mut Box::new(context))
}

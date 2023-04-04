use std::collections::HashMap;

use crate::ast::*;

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
        Expr::MacAp(macap) => {
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
        Expr::Block(x) => eval_block(x, &Box::new(clear_rules(context))),
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
                    x: eval_raw(rv, lcontext),
                    y: eval_raw(lv, lcontext),
                });
            }
        }
    }
    eval(&block.expr, lcontext)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::ast::Expr;

    use super::eval;

    fn eval_test(expr: &Expr) -> String {
        let context = Box::new(super::Context {
            symbols: HashMap::new(),
            rules: vec![],
        });
        let newexpr = Box::new(expr.clone());
        eval(&newexpr, &context)
    }

    #[test]
    fn expr_eval() {
        let expr1 = Expr::Literal(String::from("abc"));
        assert_eq!(eval_test(&expr1), "abc".to_string());
    }
}

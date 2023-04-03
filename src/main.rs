use rustyline::error::ReadlineError;
use std::env::args;

mod ast;
mod prog;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub parse); // synthesized by LALRPOP

fn main() {
    let mut argv = args();
    argv.next();
    let fp = argv.next().expect("unknown file");
    let fc = std::fs::read_to_string(fp).expect("failed to open the file");
    let res = parse::ProgramParser::new()
        .parse(fc.as_str())
        .expect("unexpected token!");
    let context = &mut Box::new(prog::Context::new());
    prog::eval_prog(res, context);

    // Rustyline
    let mut rl = rustyline::DefaultEditor::new().unwrap();
    loop {
        let line: String;
        let readline = rl.readline("> ");
        match readline {
            Ok(l) => line = l.trim().to_string(),
            Err(ReadlineError::Interrupted) => {
                println!("Interrupted");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("EOF");
                break;
            }
            Err(_) => {
                println!("invalid input");
                break;
            }
        }
        let expr = parse::ExpressionParser::new()
            .parse(line.as_str())
            .expect("invalid expression!");
        // Eval!
        let res = prog::eval(&expr, context);
        println!("{}", res);
    }
}

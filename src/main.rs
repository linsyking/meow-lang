use rustyline::error::ReadlineError;
use std::env::args;

mod ast;
mod prog;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub parse); // synthesized by LALRPOP
lalrpop_mod!(pub expr);

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

    // Print the translated program
    prog::trans_layout(context);

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
        let expr = &mut expr::ExpressionParser::new()
            .parse(line.as_str())
            .expect("invalid expression!");
        // Eval!
        let res = prog::take_one_para(expr, context);
        println!("{}", res);
    }
}

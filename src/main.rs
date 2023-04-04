use std::path::PathBuf;

use rustyline::error::ReadlineError;

mod ast;
mod cat;
mod eval;
mod prog;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub parse);
lalrpop_mod!(pub expr);

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let fp = args.get(1).expect("unknown command");
    if fp == "repl" {
        repl(&mut Box::new(prog::Context::new()));
    } else {
        let fc = std::fs::read_to_string(fp).expect("failed to open the file");
        let res = parse::ProgramParser::new()
            .parse(fc.as_str())
            .expect("unexpected token!");
        let context = &mut Box::new(prog::Context::new());
        prog::eval_prog(&res, context);
        let trans = prog::translate(&res, context);
        // Write the new code to .cat file
        let mut path = PathBuf::from(fp);
        path.set_extension("cat");
        // Write
        std::fs::write(path, trans).unwrap();
    }
}

fn repl(context: &mut Box<prog::Context>) {
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
        if &line.as_str()[0..1] == ":" {
            // command
            let cmds: Vec<&str> = line.as_str()[1..].split(" ").collect();
            let cmd = cmds.get(0).unwrap();
            // let remain = cmds.get(1..).unwrap().join(" ");
            if cmd == &"quit" {
                break;
            } else if cmd == &"clear" {
                context.clean();
            } else if cmd == &"load" {
                let path = cmds.get(1).unwrap();
                let fc = std::fs::read_to_string(path).expect("failed to open the file");
                let res = parse::ProgramParser::new()
                    .parse(fc.as_str())
                    .expect("unexpected token!");
                prog::eval_prog(&res, context);
                println!("loaded {}", path);
            } else {
                println!("unknown command");
            }
            continue;
        }
        let expr = &mut expr::ExpressionParser::new()
            .parse(line.as_str())
            .expect("invalid expression!");
        // Eval!
        let res = cat::eval(&context.macros, expr);
        println!("{}", res);
    }
}

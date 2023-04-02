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
    loop {
        let mut line = String::new();
        eprint!("> ");
        std::io::stdin().read_line(&mut line).unwrap();
        line = line.trim().to_string();
        let expr = parse::ExpressionParser::new()
            .parse(line.as_str())
            .expect("invalid expression!");
        // Eval!
        let res = prog::eval(&expr, context);
        println!("{}", res);
    }
}

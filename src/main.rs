use std::env::args;

pub mod ast;

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
    println!("{:?}", res);
}

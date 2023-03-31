pub mod ast;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub parse); // synthesized by LALRPOP

fn main() {
    let res = parse::ProgramParser::new()
        .parse(
            r#"hh() { "dd" }
            sdf(hhs, fff) {
                "fd" = hhg("ss");
                var ldk = {
                    var s = ("ff" + hhs + "d");
                    "hhh"
                };
                "ffs"
            }"#,
        )
        .expect("Not expected!");
    println!("{:?}", res);
}

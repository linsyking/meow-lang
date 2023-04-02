#[derive(Debug, Clone)]
pub enum Prog {
    Stmts(Stmt, Box<Prog>),
    Epsilon,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub name: String,
    pub args: Vec<String>,
    pub block: Box<Block>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(String),
    Cat(Box<Expr>, Box<Expr>),
    MacAp(MacAp),
    Var(String),
    Block(Box<Block>),
}

#[derive(Debug, Clone)]
pub struct MacAp {
    pub name: String,
    pub args: Vec<Box<Expr>>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub bstmts: Vec<Box<BStmt>>,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone)]
pub enum BStmt {
    MEq(Box<Expr>, Box<Expr>),
    VarDefine(String, Box<Expr>),
}

#[test]
fn tt() {
    // let dd = Stmt{name: "ss", args: [], }
    let mut xx = vec![String::from("sdsds")];
    xx.push(String::from("sdsd"));
}

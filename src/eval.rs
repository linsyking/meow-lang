use crate::ast::Tok;

#[derive(Debug, Clone)]
pub struct Macro {
    pub args: Vec<String>,
    pub body: Vec<Tok>,
}

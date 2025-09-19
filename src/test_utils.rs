use crate::syntax::{Expr, Prog};
use crate::parser;

pub fn parse_expr(s: &str) -> Result<Expr, String> {
    parser::parse_expr(s).map_err(|e| format!("Parse error: {:?}", e))
}

pub fn parse_prog(s: &str) -> Result<Prog, String> {
    parser::parse_prog(s).map_err(|e| format!("Parse error: {:?}", e))
}
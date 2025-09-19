use crate::{code_builder::{add, get_basic, load_c, mk_basic, sub, symbolic_addr}, syntax::{Expr, Range, Ty}};
use im::{HashMap, Vector, vector};
use crate::code_builder as instr;

pub struct AddressGenerator {
    next_addr: u16,
}

impl AddressGenerator {
    pub fn new() -> Self {
        AddressGenerator { next_addr: 0 }
    }

    pub fn fresh_addr(&mut self) -> u16 {
        let addr = self.next_addr;
        self.next_addr += 1;
        addr
    }
}

#[derive(Debug, Clone)]
pub enum Address {
    Local(i16),
    Global(u16),
}

#[derive(Debug, Clone)]
pub struct VarContextEntry {
    pub address: Address,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct Context {
    pub var_ctxt: HashMap<String, VarContextEntry>,
    pub ty_ctxt: HashMap<String, Ty>,
    pub constructor_ctxt: HashMap<String, Ty>,
    pub tail_pos: Option<i32>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            var_ctxt: HashMap::new(),
            ty_ctxt: HashMap::new(),
            constructor_ctxt: HashMap::new(),
            tail_pos: None,
        }
    }
}

pub fn get_var(
    ctxt: &Context,
    var_name: &str,
    var_rng: &Range,
    stack_level: i16,
) -> Result<(Ty, i32), (String, Range)> {
    match ctxt.var_ctxt.get(var_name) {
        Some(VarContextEntry{ address: Address::Local(i), ty }) => {
            Ok((
                ty.clone(),
                instr::push_loc(stack_level - i)
            ))
        },
        Some(VarContextEntry{ address: Address::Global(i), ty }) => {
            Ok((
                ty.clone(),
                instr::push_global(*i)
            ))
        },
        None => {
            Err((
                format!("identifier '{}' not found", var_name),
                var_rng.clone()
            ))
        }
    }
}

pub fn bin_op_b(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    e1: &Expr,
    e2: &Expr,
    instr: i32,
    stack_level: i16,
) -> Result<(Ty, Vector<i32>), (String, Range)> {
    let (ty1, code1) = code_b(ctxt, addr_gen, e1, stack_level)?;
    let (ty2, code2) = code_b(ctxt, addr_gen, e2, stack_level)?;
    match ty1 {
        Ty::IntTy(_) => { },
        _ => { return Err(("Expected lhs to have type 'int'".to_string(), *e1.range())); }
    };
    match ty2 {
        Ty::IntTy(_) => { },
        _ => { return Err(("Expected rhs to have type 'int'".to_string(), *e2.range())); }
    };
    Ok((
        Ty::IntTy(Range::dummy()),
        code1 + code2 + vector![instr]
    ))
}

pub fn bin_op_v(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    e1: &Expr,
    e2: &Expr,
    instr: i32,
    stack_level: i16,
) -> Result<(Ty, Vector<i32>), (String, Range)> {
    let (ty, code) = bin_op_b(ctxt, addr_gen, e1, e2, instr, stack_level)?;
    Ok((
        ty,
        code + vector![mk_basic()]
    ))
}

pub fn code_c(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    expr: &Expr,
    stack_level: i16,
) -> Result<(Ty, Vector<i32>), String> {
    panic!("code_c not implemented")
}

pub fn code_b(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    expr: &Expr,
    stack_level: i16,
) -> Result<(Ty, Vector<i32>), (String, Range)> {
    match expr {
        Expr::Int(n, _) => {
            Ok((
                Ty::IntTy(Range::dummy()),
                vector![load_c(*n)]
            ))
        },
        Expr::Plus(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::add(), stack_level)
        },
        Expr::Minus(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::sub(), stack_level)
        },
        Expr::Times(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::mul(), stack_level)
        },
        Expr::Eq(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::eq(), stack_level)
        },
        Expr::Leq(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::leq(), stack_level)
        },
        Expr::Geq(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::geq(), stack_level)
        },
        Expr::Lt(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::lt(), stack_level)
        },
        Expr::Gt(e1, e2, _) => {
            bin_op_b(ctxt, addr_gen, e1, e2, instr::gt(), stack_level)
        },
        Expr::IfThenElse{cond, then_expr, else_expr, ..} => {
            let (ty_cond, code_cond) = code_b(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                cond,
                stack_level
            )?;
            let (ty_then, code_then) = code_b(ctxt, addr_gen, then_expr, stack_level)?;
            let (ty_else, code_else) = code_b(ctxt, addr_gen, else_expr, stack_level)?;
            match ty_cond {
                Ty::IntTy(_) => { },
                _ => { return Err(("expected condition to have type 'int'".to_string(), *cond.range())); }
            }
            if !Ty::is_equal(&ty_then, &ty_else) {
                return Err(("expected 'then' and 'else' branch to have equal types".to_string(), *expr.range()));
            }
            let else_addr = addr_gen.fresh_addr();
            let after_addr = addr_gen.fresh_addr();
            Ok((
                ty_then,
                (
                    code_cond +
                    vector![instr::jump_z(else_addr)] +
                    code_then +
                    vector![instr::jump(after_addr)] +
                    vector![instr::symbolic_addr(else_addr)] +
                    code_else +
                    vector![instr::symbolic_addr(after_addr)]

                )
            ))
        },
        Expr::FunAbstraction{formals:_, body:_, range:_} => panic!("functions do not produce basic values"),
        _ => {
            let (ty, code) = code_v(ctxt, addr_gen, expr, stack_level)?;
            Ok((
                ty,
                code + vector![instr::get_basic()]
            ))
        }
    }
}

pub fn code_v(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    expr: &Expr,
    stack_level: i16,
) -> Result<(Ty, Vector<i32>), (String, Range)> {
    match expr {
        Expr::Int(n, _) => {
            Ok((
                Ty::IntTy(Range::dummy()),
                vector![load_c(*n), mk_basic()]
            ))
        },
        Expr::Plus(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::add(), stack_level)
        },
        Expr::Minus(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::sub(), stack_level)
        },
        Expr::Times(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::mul(), stack_level)
        },
        Expr::Eq(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::eq(), stack_level)
        },
        Expr::Leq(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::leq(), stack_level)
        },
        Expr::Geq(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::leq(), stack_level)
        },
        Expr::Lt(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::lt(), stack_level)
        },
        Expr::Gt(e1, e2, _) => {
            bin_op_v(ctxt, addr_gen, e1, e2, instr::gt(), stack_level)
        },
        Expr::IfThenElse{cond, then_expr, else_expr, ..} => {
            let (ty_cond, code_cond) = code_b(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                cond,
                stack_level
            )?;
            let (ty_then, code_then) = code_v(ctxt, addr_gen, then_expr, stack_level)?;
            let (ty_else, code_else) = code_v(ctxt, addr_gen, else_expr, stack_level)?;
            match ty_cond {
                Ty::IntTy(_) => { },
                _ => { return Err(("expected condition to have type 'int'".to_string(), *cond.range())); }
            }
            if !Ty::is_equal(&ty_then, &ty_else) {
                return Err(("expected 'then' and 'else' branch to have equal types".to_string(), *expr.range()));
            }
            let else_addr = addr_gen.fresh_addr();
            let after_addr = addr_gen.fresh_addr();
            Ok((
                ty_then,
                (
                    code_cond +
                    vector![instr::jump_z(else_addr)] +
                    code_then +
                    vector![instr::jump(after_addr)] +
                    vector![instr::symbolic_addr(else_addr)] +
                    code_else +
                    vector![instr::symbolic_addr(after_addr)]
                )
            ))
        },
        Expr::Let{ bound_var, bind_to, body, .. } => {
            let (ty_bound, code_bound) = code_v(ctxt, addr_gen, bind_to, stack_level)?;
            let var_entry = VarContextEntry { address: Address::Local(stack_level + 1), ty: ty_bound };
            let ctxt_2 = Context { var_ctxt: ctxt.var_ctxt.update(bound_var.clone(), var_entry), ..ctxt.clone() };
            let (ty_body, code_body) = code_v(&ctxt_2, addr_gen, body, stack_level + 1)?;
            Ok((
                ty_body,
                code_bound + code_body + vector![instr::slide(1, 1)]
            ))
        },
        Expr::Var(name, rng) => {
            let (ty, push_var_instr) = get_var(ctxt, name, rng, stack_level)?;
            Ok((
                ty,
                vector![push_var_instr, instr::eval()]
            ))
        },
        _ => panic!("not implemented")
    }
}
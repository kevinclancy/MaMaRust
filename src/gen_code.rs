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
        Expr::FunAbstraction { formals, body, range } => {
            let free_var_list : Vec<String> = expr.free_vars().iter().cloned().collect();
            let global_vars : Vec<(Ty, i32)> = free_var_list.iter().enumerate().map(
                |(i, var)| get_var(ctxt, var, range, stack_level + i as i16)
            ).collect::<Result<Vec<_>, _>>()?;
            let push_globals : Vector<i32> = global_vars.iter().map(|(_, instr)| *instr).collect();
            let execute_body_addr = addr_gen.fresh_addr();
            let after_addr = addr_gen.fresh_addr();

            let mut body_ctxt = ctxt.clone();
            for (i, formal) in formals.iter().enumerate() {
                let var_entry = VarContextEntry {
                    address: Address::Local(-(i as i16)),
                    ty: formal.ty.clone()
                };
                body_ctxt.var_ctxt = body_ctxt.var_ctxt.update(formal.name.clone(), var_entry);
            }
            for (i, (var_name, (ty, _))) in free_var_list.iter().zip(global_vars.iter()).enumerate() {
                let var_entry = VarContextEntry {
                    address: Address::Global(i as u16),
                    ty: ty.clone()
                };
                body_ctxt.var_ctxt = body_ctxt.var_ctxt.update(var_name.clone(), var_entry);
            }

            let (body_ty, body_code) = code_v(&body_ctxt, addr_gen, body, 0)?;

            let fun_ty = formals.iter().rev().fold(body_ty, |acc, formal| {
                Ty::FunTy {
                    dom: Box::new(formal.ty.clone()),
                    cod: Box::new(acc),
                    range: Range::dummy()
                }
            });
            Ok((
                fun_ty,
                (
                    push_globals +
                    vector![
                        instr::mk_vec(global_vars.len() as u16),
                        instr::mk_fun_val(execute_body_addr),
                        instr::jump(after_addr),
                        instr::symbolic_addr(execute_body_addr),
                        instr::targ(formals.len() as u8)
                    ] +
                    body_code +
                    vector![
                        instr::return_(formals.len() as u8),
                        instr::symbolic_addr(after_addr)
                    ]
                )
            ))
        },
        Expr::Application { fn_expr, args, .. } => {
            let num_admin_elems = match ctxt.tail_pos { Some(_) => 0i16, None => 1i16 };
            let (ty_fun, code_fun) =
                code_v(ctxt, addr_gen, fn_expr, stack_level + (args.len() as i16) + num_admin_elems)?;
            let ty_code_args: Vec<(Ty, Vector<i32>)> = args.iter().enumerate().map(
                |(i, e)|
                    code_v(
                        &Context { tail_pos: None, ..ctxt.clone() },
                        addr_gen,
                        e,
                        stack_level + ((args.len() - i - 1) as i16) + num_admin_elems
                    )
            ).collect::<Result<Vec<_>, _>>()?;
            let formal_tys = ty_fun.dom_ty_list();
            if formal_tys.len() < ty_code_args.len() {
                return Err(("expected applied expression to have function type".to_string(), *fn_expr.range()))
            }
            let used_formal_tys : Vec<Ty> = formal_tys.iter().take(ty_code_args.len()).cloned().collect();
            for i in 0..ty_code_args.len() {
                let (actual_ty, _) = &ty_code_args[i];
                let formal_ty = &used_formal_tys[i];
                if !Ty::is_equal(actual_ty, formal_ty) {
                    return Err(("argument type mismatch".to_string(), *args[i].range()));
                }
            }
            let arg_codes: Vector<i32> = ty_code_args.iter().fold(Vector::new(), |acc, (_, code)| acc + code.clone());
            let result_ty = formal_tys.iter().skip(ty_code_args.len()).fold(
                ty_fun.apply(ty_code_args.len()),
                |acc, formal_ty| Ty::FunTy {
                    dom: Box::new(formal_ty.clone()),
                    cod: Box::new(acc),
                    range: Range::dummy()
                }
            );
            match ctxt.tail_pos {
                Some(num_formals) if ty_code_args.len() == num_formals as usize => {
                    Ok((
                        result_ty,
                        arg_codes + code_fun + vector![instr::slide(ty_code_args.len() as u8, 1), instr::apply()]
                    ))
                },
                _ => {
                    let after_addr = addr_gen.fresh_addr();
                    Ok((
                        result_ty,
                        (
                            vector![instr::mark(after_addr)] +
                            arg_codes +
                            code_fun +
                            vector![
                                instr::apply(),
                                instr::symbolic_addr(after_addr)
                            ]
                        )
                    ))
                }
            }
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
use crate::{code_builder::{add, get_basic, load_c, mk_basic, mk_vec, sub, symbolic_addr}, syntax::{Expr, Pattern, Prog, Span, Ty, Typedef, dummy_span}};
use im::{HashMap, Vector, vector};
use crate::code_builder as instr;

/// An object that generates a sequence of unique symbolic addresses
pub struct AddressGenerator {
    /// The next address to generate
    next_addr: u16,
}

impl AddressGenerator {
    pub fn new() -> Self {
        AddressGenerator { next_addr: 0 }
    }

    /// Returns a symbolic address that is unique from all other symbolic addresses that
    /// have been returned by this `AddressGenerator`
    pub fn fresh_addr(&mut self) -> u16 {
        let addr = self.next_addr;
        self.next_addr += 1;
        addr
    }
}

/// The physical location of a value
#[derive(Debug, Clone)]
pub enum Address {
    /// `Local(n)` contains the address's offset from SP0 (the SP when the most recent function was called)
    ///
    /// Postive `n` is for let-bound values, with higher values of `n` for more recent bindings
    ///
    /// Non-positive `n` is for function call arguments; 0 is the leftmost-argument, 1 is the next argument, etc.
    Local(i16),
    /// `Global(n)` locates the `n`th variable stored in global vector (0-indexed); this is used to store values
    /// in a function's closure
    Global(u16),
}

#[derive(Debug, Clone)]
pub struct VarContextEntry {
    /// The address of the variable
    pub address: Address,
    /// The type of the value bound to the variable
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct ConstructorSig {
    /// Field names and types in the order they appear in the typedef declaration
    fields : Vec<(String, Ty)>,
    /// The name of the discriminated union type being constructed
    ty_id : String,
    /// An integer that identifies that variant among all variants of type `ty_id`
    variant_id : u16
}

/// Contextual information relevant to a position in source code.
/// This includes types of bound variables and other things.
#[derive(Debug, Clone)]
pub struct Context {
    /// Maps each variable name in context to its address and type
    pub var_ctxt: HashMap<String, VarContextEntry>,
    pub ty_ctxt: HashMap<String, Ty>,
    pub constructor_ctxt: HashMap<String, ConstructorSig>,
    /// Some(n) if we're in tail position in an n-parameter function definition, None otherwise
    pub tail_pos: Option<u8>,
    pub fail_addr: u16
}

impl Context {
    pub fn new(fail_addr: u16) -> Self {
        Context {
            var_ctxt: HashMap::new(),
            ty_ctxt: HashMap::new(),
            constructor_ctxt: HashMap::new(),
            tail_pos: None,
            fail_addr
        }
    }
}

/// Process a list of typedefs, registering each type and its constructors in the context.
pub fn process_typedefs(ctxt: &mut Context, typedefs: &[Typedef]) -> Result<(), (String, Span)> {
    for typedef in typedefs {
        let sum_variants: std::collections::HashMap<String, Vec<(String, Ty)>> = typedef.variants.iter().map(|v| {
            let fields: Vec<(String, Ty)> = v.fields.iter().map(|(name, ty, _)| (name.clone(), ty.clone())).collect();
            (v.constructor_name.clone(), fields)
        }).collect();
        let sum_ty = Ty::SumTy {
            variants: sum_variants,
            range: typedef.range.clone(),
        };
        ctxt.ty_ctxt = ctxt.ty_ctxt.update(typedef.typename.clone(), sum_ty);
        for (i, variant) in typedef.variants.iter().enumerate() {
            let fields: Vec<(String, Ty)> = variant.fields.iter().map(|(name, ty, _)| {
                (name.clone(), ty.clone())
            }).collect();
            let sig = ConstructorSig {
                fields,
                ty_id: typedef.typename.clone(),
                variant_id: i as u16,
            };
            ctxt.constructor_ctxt = ctxt.constructor_ctxt.update(variant.constructor_name.clone(), sig);
        }
    }
    Ok(())
}

/// Generate code for a complete program: process typedefs to build the context,
/// then generate code for the body expression.
pub fn gen_code_prog(prog: &Prog) -> Result<(Ty, Vector<i32>), (String, Span)> {
    let mut addr_gen = AddressGenerator::new();
    let fail_addr = addr_gen.fresh_addr();
    let fail_code = vector![instr::symbolic_addr(fail_addr), instr::halt()];
    let mut ctxt = Context::new(fail_addr);
    process_typedefs(&mut ctxt, &prog.typedefs)?;
    let (ty, code) = code_v(&ctxt, &mut addr_gen, &prog.expr, 0)?;
    Ok((ty, code + fail_code))
}

/// If the variable `var_name` is in context, return its type and an instruction
/// that pushes the value it refers to onto the stack
///
/// If `var_name` is not in context, generate a type-checking error using the `Err` variant.
pub fn get_var(
    ctxt: &Context,
    var_name: &str,
    var_rng: &Span,
    stack_level: u8,
) -> Result<(Ty, i32), (String, Span)> {
    match ctxt.var_ctxt.get(var_name) {
        Some(VarContextEntry{ address: Address::Local(i), ty }) => {
            Ok((
                ty.clone(),
                instr::push_loc(stack_level as i16 - i)
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

/// Generate code to push the value (NOT a heap reference) of `e1 instr_op e2` onto the stack,
/// where `instr_op` is the operation performed by the instruction `instr`
///
/// If either `e1` or `e2` do not match the expected types of the arguments of `instr_op` then
/// generate a type error.
pub fn bin_op_b(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    e1: &Expr,
    e2: &Expr,
    instr: i32,
    stack_level: u8,
) -> Result<(Ty, Vector<i32>), (String, Span)> {
    let ctxt_prime = Context { tail_pos: None, ..ctxt.clone() };
    let (ty1, code1) = code_b(&ctxt_prime, addr_gen, e1, stack_level)?;
    let (ty2, code2) = code_b(&ctxt_prime, addr_gen, e2, stack_level)?;
    match ty1 {
        Ty::IntTy(_) => { },
        _ => { return Err(("Expected lhs to have type 'int'".to_string(), e1.range().clone())); }
    };
    match ty2 {
        Ty::IntTy(_) => { },
        _ => { return Err(("Expected rhs to have type 'int'".to_string(), e2.range().clone())); }
    };
    Ok((
        Ty::IntTy(0..0),
        code1 + code2 + vector![instr]
    ))
}

/// Letting `instr_op` by the operation performed by the instruction `instr`, generates code to:
/// 1. Allocate a basic value on the heap,
/// 2. Store the value of `e1 instr_op e2` in the basic value
/// 3. Push a reference to the basic value onto the stack
///
/// If either `e1` or `e2` do not match the expected types of the arguments of `instr_op`, then
/// generate a type error.
pub fn bin_op_v(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    e1: &Expr,
    e2: &Expr,
    instr: i32,
    stack_level: u8,
) -> Result<(Ty, Vector<i32>), (String, Span)> {
    let (ty, code) = bin_op_b(ctxt, addr_gen, e1, e2, instr, stack_level)?;
    Ok((
        ty,
        code + vector![mk_basic()]
    ))
}

/// Closure generation. This is not implemented for now, because our language is CBV. We will implement it later
/// when we introduce controlled lazy evaluation ala OCaml.
pub fn code_c(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    expr: &Expr,
    stack_level: u8,
) -> Result<(Ty, Vector<i32>), String> {
    panic!("code_c not implemented")
}

/// Assuming `expr` computes a basic value, generate code to push the value (NOT a heap reference)
/// directly onto the stack
///
/// Returns a type error if `expr` is ill-typed
pub fn code_b(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    expr: &Expr,
    stack_level: u8,
) -> Result<(Ty, Vector<i32>), (String, Span)> {
    match expr {
        Expr::Int(n, _) => {
            Ok((
                Ty::IntTy(0..0),
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
                _ => { return Err(("expected condition to have type 'int'".to_string(), cond.range().clone())); }
            }
            if !Ty::is_equal(&ty_then, &ty_else) {
                return Err(("expected 'then' and 'else' branch to have equal types".to_string(), expr.range().clone()));
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
        Expr::FunAbstraction{formals:_, body:_, range:_} =>
            panic!("functions do not produce basic values"),
        _ => {
            let (ty, code) = code_v(ctxt, addr_gen, expr, stack_level)?;
            Ok((
                ty,
                code + vector![instr::get_basic()]
            ))
        }
    }
}

/// Generate code to push the value denoted by the expression `expr` onto the stack.
///
/// If `expr` has a type error then report it using the `Err` variant
pub fn code_v(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    expr: &Expr,
    stack_level: u8,
) -> Result<(Ty, Vector<i32>), (String, Span)> {
    match expr {
        Expr::Int(n, _) => {
            Ok((
                Ty::IntTy(0..0),
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
                _ => { return Err(("expected condition to have type 'int'".to_string(), cond.range().clone())); }
            }
            if !Ty::is_equal(&ty_then, &ty_else) {
                return Err(("expected 'then' and 'else' branch to have equal types".to_string(), expr.range().clone()));
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
                |(i, var)| get_var(ctxt, var, range, stack_level + (i as u8))
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
            let body_ctxt = &Context{ tail_pos: Some(formals.len() as u8), ..body_ctxt };
            let (body_ty, body_code) = code_v(body_ctxt, addr_gen, body, 0)?;

            let fun_ty = formals.iter().rev().fold(body_ty, |acc, formal| {
                Ty::FunTy {
                    dom: Box::new(formal.ty.clone()),
                    cod: Box::new(acc),
                    range: 0..0
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
            let num_admin_elems = match ctxt.tail_pos { Some(_) => 0u8, None => 1u8 };
            let (ty_fun, code_fun) =
                code_v(ctxt, addr_gen, fn_expr, stack_level + (args.len() as u8) + num_admin_elems)?;
            let ty_code_args: Vec<(Ty, Vector<i32>)> = args.iter().enumerate().map(
                |(i, e)|
                    code_v(
                        &Context { tail_pos: None, ..ctxt.clone() },
                        addr_gen,
                        e,
                        stack_level + ((args.len() - i - 1) as u8) + num_admin_elems
                    )
            ).collect::<Result<Vec<_>, _>>()?;
            let formal_tys = ty_fun.dom_ty_list();
            if formal_tys.len() < ty_code_args.len() {
                return Err(("expected applied expression to have function type".to_string(), fn_expr.range().clone()))
            }
            let used_formal_tys : Vec<Ty> = formal_tys.iter().take(ty_code_args.len()).cloned().collect();
            for i in 0..ty_code_args.len() {
                let (actual_ty, _) = &ty_code_args[i];
                let formal_ty = &used_formal_tys[i];
                if !Ty::is_equal(actual_ty, formal_ty) {
                    return Err(("argument type mismatch".to_string(), args[i].range().clone()));
                }
            }
            let arg_codes: Vector<i32> = ty_code_args.iter().rev().fold(
                Vector::new(),
                |acc, (_, code)| acc + code.clone()
            );
            match ctxt.tail_pos {
                Some(num_formals) if ty_code_args.len() == num_formals as usize => {
                    Ok((
                        ty_fun.apply(args.len()),
                        (
                            arg_codes +
                            code_fun +
                            vector![
                                instr::slide(stack_level + num_formals, args.len() as u8 + 1),
                                instr::apply()
                            ]
                        )
                    ))
                },
                _ => {
                    let after_addr = addr_gen.fresh_addr();
                    Ok((
                        ty_fun.apply(args.len()),
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
        Expr::Tuple(exprs, _) => {
            let (component_tys, component_codes) : (Vec<Ty>, Vec<Vector<i32>>) = exprs.iter().enumerate().map(
                |(i, expr)| {
                    let (ty, code) = code_v(ctxt, addr_gen, expr, stack_level + (i as u8))?;
                    Ok((ty, code))
                }
            ).collect::<Result<Vec<_>, _>>()?.into_iter().unzip();
            let n = component_codes.len() as u16;
            let push_components_code : Vector<i32> = component_codes.into_iter().sum();
            Ok((
                Ty::ProdTy { components: component_tys, range: dummy_span() },
                push_components_code + vector![mk_vec(n)]
            ))
        },
        Expr::LetTuple{ component_vars, bind_to, body, range:_ } => {
            let num_components = component_vars.len();
            let (ty_bind_to, code_bind_to) = code_v(ctxt, addr_gen, bind_to, stack_level)?;
            let Ty::ProdTy { components: ty_components, range: _ } = ty_bind_to else {
                return Err(("scrutinee expected to have tuple type".to_string(), bind_to.range().clone()))
            };
            if ty_components.len() != component_vars.len() {
                return Err(("Wrong number of tuple components".to_string(), bind_to.range().clone()))
            }
            let var_ctxt_2 = component_vars.iter().enumerate().fold(ctxt.var_ctxt.clone(),
                |acc, (i, var_name)| {
                    acc.update(
                        var_name.clone(),
                         VarContextEntry {
                            address: Address::Local(stack_level as i16 + i as i16 + 1),
                            ty: ty_components[i].clone()
                        }
                    )
                }
            );
            let ctxt_2 = Context { var_ctxt: var_ctxt_2, ..ctxt.clone() };
            let (ty_body, code_body) = code_v(&ctxt_2, addr_gen, body, stack_level + (num_components as u8))?;
            Ok((
                ty_body,
                code_bind_to + vector![instr::get_vec()] + code_body + vector![instr::slide(num_components as u8,1)]
            ))
        },
        Expr::Let{ bound_pat, bind_to, body, .. } => {
            let (ty_bound, code_bound) = code_v(ctxt, addr_gen, bind_to, stack_level)?;
            let (pattern_code, ctxt_2, num_bindings) = code_pattern(
                ctxt,
                addr_gen,
                bound_pat,
                &ty_bound,
                ctxt.fail_addr,
                0,
                stack_level+1,
                stack_level+1
            )?;
            let (ty_body, code_body) = code_v(&ctxt_2, addr_gen, body, stack_level + 1 + num_bindings)?;
            Ok((
                ty_body,
                code_bound + pattern_code + code_body + vector![instr::slide(1, num_bindings + 1)]
            ))
        },
        Expr::Var(name, rng) => {
            let (ty, push_var_instr) = get_var(ctxt, name, rng, stack_level)?;
            Ok((
                ty,
                vector![push_var_instr, instr::eval()]
            ))
        },
        Expr::LetRec { bindings, body, .. } => {
            let n = bindings.len();
            let ctxt_prime = bindings.iter().enumerate().fold(ctxt.clone(), |acc_ctxt, (i, (name, ty, _))| {
                let var_entry = VarContextEntry {
                    address: Address::Local(stack_level as i16 + (i as i16) + 1),
                    ty: ty.clone()
                };
                Context {
                    var_ctxt: acc_ctxt.var_ctxt.update(name.clone(), var_entry),
                    ..acc_ctxt
                }
            });
            let binding_codes: Vec<(Ty, Vector<i32>)> = bindings.iter()
                .map(|(_, ascribed_ty, bound_expr)| {
                    let (synthesized_ty, bound_code) = code_v(
                        &Context { tail_pos: None, ..ctxt_prime.clone() },
                        addr_gen,
                        bound_expr,
                        stack_level + (n as u8)
                    )?;

                    if !Ty::is_equal(&synthesized_ty, ascribed_ty) {
                        return Err((
                            format!("ascribed type does not match synthesized type"),
                            bound_expr.range().clone()
                        ));
                    }

                    Ok((synthesized_ty, bound_code))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let (body_ty, body_code) = code_v(&ctxt_prime, addr_gen, body, stack_level + (n as u8))?;
            let rewrite_blocks = binding_codes.iter().enumerate()
                .rev()
                .fold(Vector::new(), |acc, (i, (_, bound_code))| {
                    let rewrite_idx = (i + 1) as u8;
                    acc + bound_code.clone() + vector![instr::rewrite(rewrite_idx)]
                });
            Ok((
                body_ty,
                vector![instr::alloc(n as u8)] + rewrite_blocks + body_code + vector![instr::slide(n as u8, 1)]
            ))
        },
        Expr::RefConstructor { init, .. } => {
            let (init_ty, init_code) = code_v(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                init,
                stack_level
            )?;
            Ok((
                Ty::RefTy { contained_ty: Box::new(init_ty), range: 0..0 },
                init_code + vector![instr::mk_ref()]
            ))
        },
        Expr::Deref { ref_expr, range } => {
            let (ref_expr_ty, ref_expr_code) = code_v(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                ref_expr,
                stack_level
            )?;
            let elem_ty = match ref_expr_ty {
                Ty::RefTy { contained_ty, .. } => *contained_ty,
                _ => {
                    return Err((
                        format!("Expected {:?} to have a reference type but instead found {}", ref_expr, ref_expr_ty),
                        range.clone()
                    ));
                }
            };
            Ok((
                elem_ty,
                ref_expr_code + vector![instr::get_ref()]
            ))
        },
        Expr::Assign { ref_expr, new_val, range } => {
            let (new_val_ty, new_val_code) = code_v(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                new_val,
                stack_level
            )?;
            let (ref_expr_ty, ref_expr_code) = code_v(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                ref_expr,
                stack_level + 1
            )?;
            match &ref_expr_ty {
                Ty::RefTy { contained_ty, .. } => {
                    if !Ty::is_equal(&*contained_ty, &new_val_ty) {
                        return Err((
                            format!("expected lhs to have type Ref {} but instead had type {}", new_val_ty, ref_expr_ty),
                            range.clone()
                        ));
                    }
                },
                _ => {
                    return Err((
                        format!("expected lhs to have reference type but instead had type {}", ref_expr_ty),
                        range.clone()
                    ));
                }
            }
            Ok((
                Ty::ProdTy{ components: vec![], range: 0..0 },
                new_val_code + ref_expr_code + vector![instr::ref_assign()]
            ))
        },
        Expr::ConstructorApplication { name, fields, range } => {
            let sig = ctxt.constructor_ctxt.get(name).ok_or_else(|| {
                (format!("unknown constructor '{}'", name), range.clone())
            })?;
            let sig = sig.clone();
            if fields.len() != sig.fields.len() {
                return Err((
                    format!("constructor '{}' expects {} fields, got {}", name, sig.fields.len(), fields.len()),
                    range.clone()
                ));
            }
            let mut field_codes: Vector<i32> = Vector::new();
            for (i, (field_name, field_expr, field_span)) in fields.iter().enumerate() {
                let expected_ty = sig.fields.iter()
                    .find(|(n, _)| n == field_name)
                    .map(|(_, ty)| ty)
                    .ok_or_else(|| {
                        (format!("constructor '{}' has no field '{}'", name, field_name), field_span.clone())
                    })?;
                let (actual_ty, code) = code_v(
                    &Context { tail_pos: None, ..ctxt.clone() },
                    addr_gen,
                    field_expr,
                    stack_level + (i as u8)
                )?;
                if !Ty::is_equal(&actual_ty, expected_ty) {
                    return Err((
                        format!("field '{}' expected type {}, got {}", field_name, expected_ty, actual_ty),
                        field_span.clone()
                    ));
                }
                field_codes = field_codes + code;
            }
            Ok((
                Ty::IdTy { name: sig.ty_id.clone(), range: 0..0 },
                field_codes + vector![mk_vec(fields.len() as u16), instr::mk_sum(sig.variant_id)]
            ))
        }
        Expr::Sequence { first, second, .. } => {
            let (first_ty, first_code) = code_v(
                &Context { tail_pos: None, ..ctxt.clone() },
                addr_gen,
                first,
                stack_level
            )?;
            let (second_ty, second_code) = code_v(ctxt, addr_gen, second, stack_level)?;
            match first_ty {
                Ty::ProdTy { components, .. } if components.is_empty() => {},
                _ => {
                    return Err((
                        "expected first expression to have unit type".to_string(),
                        first.range().clone()
                    ));
                }
            }
            Ok((
                second_ty,
                first_code + vector![instr::pop()] + second_code
            ))
        },
        _ => panic!("{:?} not implemented", expr)
    }
}


/// Returns a triple (`code`, `ctxt2`, `num_pushed`) where
///
/// * `code` pushes pattern-variable-bound values onto the stack and falls through on match,
///    or jumps to `fail_addr` on mismatch (after restoring the stack to `base_stack_level`)
/// * `ctxt2` is `ctxt` extended with the pattern variables
/// * `num_pushed` is the number of values pushed to the stack
///
/// `scrut_depth` is how far below the current stack top the scrutinee sits (0 = top of stack).
/// `base_stack_level` is the absolute stack level to restore to before jumping to `fail_addr`.
/// `stack_level` is the absolute stack level used for addressing local variables.
pub fn code_pattern(
    ctxt: &Context,
    addr_gen: &mut AddressGenerator,
    pat: &Pattern,
    scrut_ty: &Ty,
    fail_addr: u16,
    scrut_depth: u8,
    base_stack_level: u8,
    stack_level: u8
) -> Result<(Vector<i32>, Context, u8), (String, Span)> {
    match pat {
        Pattern::Var(name, _) => {
            let entry = VarContextEntry { ty: scrut_ty.clone(), address: Address::Local(stack_level as i16 - scrut_depth as i16) };
            let ctxt2 = Context {
                var_ctxt: ctxt.var_ctxt.update(name.clone(), entry),
                ..ctxt.clone()
            };
            Ok((vector![], ctxt2, 0))
        },
        Pattern::Int(n, _) => {
            let success_addr = addr_gen.fresh_addr();
            let ctxt2 = ctxt.clone();
            let instrs = vector![
                instr::push_loc(scrut_depth as i16),
                instr::get_basic(),
                instr::load_c(*n),
                instr::eq(),
                instr::jump_nz(success_addr),
                instr::slide(stack_level - base_stack_level + 1, 0),
                instr::jump(fail_addr),
                instr::symbolic_addr(success_addr)
            ];
            Ok((instrs, ctxt2, 0))
        },
        Pattern::Tuple(sub_pats, span) => {
            let Ty::ProdTy { components: component_tys, .. } = scrut_ty else {
                return Err(("expected scrutinee to have tuple type".to_string(), span.clone()));
            };
            if sub_pats.len() != component_tys.len() {
                return Err((
                    format!("tuple pattern has {} components but scrutinee has {}", sub_pats.len(), component_tys.len()),
                    span.clone()
                ));
            }
            let n = sub_pats.len() as u8;
            let mut code = vector![instr::push_loc(scrut_depth as i16), instr::get_vec()];
            let mut ctxt_acc = ctxt.clone();
            let mut total_pushed: u8 = n;
            for (i, (sub_pat, component_ty)) in sub_pats.iter().zip(component_tys.iter()).enumerate() {
                let sub_depth = total_pushed - i as u8 - 1;
                let component_stack_level = stack_level + total_pushed;
                let (sub_code, ctxt2, sub_pushed) = code_pattern(
                    &ctxt_acc,
                    addr_gen,
                    sub_pat,
                    component_ty,
                    fail_addr,
                    sub_depth,
                    base_stack_level,
                    component_stack_level
                )?;
                code = code + sub_code;
                ctxt_acc = ctxt2;
                total_pushed += sub_pushed;
            }
            Ok((code, ctxt_acc, total_pushed))
        },
        Pattern::ConstructorApplication { name, fields: pat_fields, open, span } => {
            let sig = ctxt.constructor_ctxt.get(name).ok_or_else(|| {
                (format!("unknown constructor '{}'", name), span.clone())
            })?.clone();

            let resolved_scrut_ty = match scrut_ty {
                Ty::IdTy { name: ty_name, .. } => {
                    ctxt.ty_ctxt.get(ty_name).ok_or_else(|| {
                        (format!("unknown type '{}'", ty_name), span.clone())
                    })?.clone()
                },
                other => other.clone()
            };
            let Ty::SumTy { variants, .. } = &resolved_scrut_ty else {
                return Err(("expected scrutinee to have sum type".to_string(), span.clone()));
            };
            if !variants.contains_key(name) {
                return Err((
                    format!("constructor '{}' does not belong to scrutinee type", name),
                    span.clone()
                ));
            }

            let success_addr = addr_gen.fresh_addr();
            let mut code = vector![
                instr::push_loc(scrut_depth as i16),
                instr::get_tag(),
                instr::load_c(sig.variant_id as i32),
                instr::eq(),
                instr::jump_nz(success_addr),
                instr::slide(stack_level - base_stack_level + 1, 0),
                instr::jump(fail_addr),
                instr::symbolic_addr(success_addr),
                instr::push_loc(scrut_depth as i16),
                instr::tget_constructor_arg(),
                instr::get_vec()
            ];

            let n = sig.fields.len() as u8;
            let mut ctxt_acc = ctxt.clone();
            let mut total_pushed: u8 = n;
            for (i, (field_name, field_ty)) in sig.fields.iter().enumerate() {
                match pat_fields.get(field_name) {
                    Some((sub_pat, _)) => {
                        let sub_depth = total_pushed - i as u8 - 1;
                        let component_stack_level = stack_level + total_pushed;
                        let (sub_code, ctxt2, sub_pushed) = code_pattern(
                            &ctxt_acc,
                            addr_gen,
                            sub_pat,
                            field_ty,
                            fail_addr,
                            sub_depth,
                            base_stack_level,
                            component_stack_level
                        )?;
                        code = code + sub_code;
                        ctxt_acc = ctxt2;
                        total_pushed += sub_pushed;
                    },
                    None if *open => {},
                    None => {
                        return Err((
                            format!("pattern for constructor '{}' is missing field '{}'", name, field_name),
                            span.clone()
                        ));
                    }
                }
            }
            Ok((code, ctxt_acc, total_pushed))
        }
    }
}

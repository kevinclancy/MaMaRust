use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Range {
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl Range {
    pub fn new(start_line: usize, start_col: usize, end_line: usize, end_col: usize) -> Self {
        Range { start_line, start_col, end_line, end_col }
    }

    pub fn dummy() -> Self {
        Range { start_line: 0, start_col: 0, end_line: 0, end_col: 0 }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub constructor_name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    IntTy(Range),
    FunTy { dom: Box<Ty>, cod: Box<Ty>, range: Range },
    ProdTy { components: Vec<Ty>, range: Range },
    RefTy { contained_ty: Box<Ty>, range: Range },
    SumTy { variants: HashMap<String, Ty>, range: Range },
    IdTy { name: String, range: Range },
}

impl Ty {
    /// Type equality that ignores ranges
    pub fn is_equal(&self, other: &Ty) -> bool {
        match (self, other) {
            (Ty::IntTy(_), Ty::IntTy(_)) => true,
            (Ty::FunTy { dom: dom_a, cod: cod_a, .. }, Ty::FunTy { dom: dom_b, cod: cod_b, .. }) => {
                dom_a.is_equal(dom_b) && cod_a.is_equal(cod_b)
            }
            (Ty::ProdTy { components: comp_a, .. }, Ty::ProdTy { components: comp_b, .. }) => {
                comp_a.len() == comp_b.len() &&
                comp_a.iter().zip(comp_b.iter()).all(|(a, b)| a.is_equal(b))
            }
            (Ty::RefTy { contained_ty: ty_a, .. }, Ty::RefTy { contained_ty: ty_b, .. }) => {
                ty_a.is_equal(ty_b)
            }
            (Ty::SumTy { variants: var_a, .. }, Ty::SumTy { variants: var_b, .. }) => {
                var_a.len() == var_b.len() &&
                var_a.iter().all(|(name, ty_a)| {
                    var_b.get(name).map_or(false, |ty_b| ty_a.is_equal(ty_b))
                })
            }
            (Ty::IdTy { name: name_a, .. }, Ty::IdTy { name: name_b, .. }) => {
                name_a == name_b
            }
            _ => false,
        }
    }

    /// Returns a list of the types of a function type's domain
    pub fn dom_ty_list(&self) -> Vec<Ty> {
        match self {
            Ty::FunTy { dom, cod, .. } => {
                let mut result = vec![dom.as_ref().clone()];
                result.extend(cod.dom_ty_list());
                result
            }
            _ => Vec::new(),
        }
    }

    /// Apply n arguments to a function type, returning the result type
    pub fn apply(&self, n: usize) -> Ty {
        match (n, self) {
            (0, _) => self.clone(),
            (_, Ty::FunTy { cod, .. }) => cod.apply(n - 1),
            _ => panic!("applied function type to too many args"),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::IntTy(_) => write!(f, "int"),
            Ty::FunTy { dom, cod, .. } => write!(f, "{} -> {}", dom, cod),
            Ty::ProdTy { components, .. } => {
                let comp_strs: Vec<String> = components.iter().map(|c| c.to_string()).collect();
                write!(f, "({})", comp_strs.join(","))
            }
            Ty::RefTy { contained_ty, .. } => write!(f, "Ref {}", contained_ty),
            Ty::SumTy { .. } => write!(f, "sumTy"),
            Ty::IdTy { name, .. } => write!(f, "{}", name),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Typedef {
    pub typename: String,
    pub variants: Vec<Variant>,
    pub range: Range,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Formal {
    pub name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchCase {
    ConstructorCase {
        name: String,
        arg_var: String,
        when_cond: Option<Box<Expr>>,
        body: Box<Expr>,
        range: Range,
    },
    CatchAllCase {
        var_name: String,
        when_cond: Option<Box<Expr>>,
        body: Box<Expr>,
        range: Range,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Plus(Box<Expr>, Box<Expr>, Range),
    Minus(Box<Expr>, Box<Expr>, Range),
    Times(Box<Expr>, Box<Expr>, Range),
    Eq(Box<Expr>, Box<Expr>, Range),
    Leq(Box<Expr>, Box<Expr>, Range),
    Geq(Box<Expr>, Box<Expr>, Range),
    Lt(Box<Expr>, Box<Expr>, Range),
    Gt(Box<Expr>, Box<Expr>, Range),
    FunAbstraction {
        formals: Vec<Formal>,
        body: Box<Expr>,
        range: Range,
    },
    Var(String, Range),
    Let {
        bound_var: String,
        bind_to: Box<Expr>,
        body: Box<Expr>,
        range: Range,
    },
    LetRec {
        bindings: Vec<(String, Ty, Expr)>,
        body: Box<Expr>,
        range: Range,
    },
    Application {
        fn_expr: Box<Expr>,
        args: Vec<Expr>,
        range: Range,
    },
    ConstructorApplication {
        name: String,
        arg: Box<Expr>,
        range: Range,
    },
    Match {
        scrutinee: Box<Expr>,
        cases: Vec<MatchCase>,
        range: Range,
    },
    IfThenElse {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        range: Range,
    },
    Int(i32, Range),
    Tuple(Vec<Expr>, Range),
    LetTuple {
        component_vars: Vec<String>,
        bind_to: Box<Expr>,
        body: Box<Expr>,
        range: Range,
    },
    RefConstructor {
        init: Box<Expr>,
        range: Range,
    },
    Deref {
        ref_expr: Box<Expr>,
        range: Range,
    },
    Assign {
        ref_expr: Box<Expr>,
        new_val: Box<Expr>,
        range: Range,
    },
    Sequence {
        first: Box<Expr>,
        second: Box<Expr>,
        range: Range,
    },
}

impl Expr {
    pub fn range(&self) -> &Range {
        match self {
            Expr::Plus(_, _, rng) | Expr::Minus(_, _, rng) | Expr::Times(_, _, rng)
            | Expr::Eq(_, _, rng) | Expr::Leq(_, _, rng) | Expr::Geq(_, _, rng)
            | Expr::Lt(_, _, rng) | Expr::Gt(_, _, rng) | Expr::Var(_, rng)
            | Expr::Int(_, rng) | Expr::Tuple(_, rng) => rng,
            Expr::FunAbstraction { range, .. } | Expr::Let { range, .. }
            | Expr::LetRec { range, .. } | Expr::Application { range, .. }
            | Expr::ConstructorApplication { range, .. } | Expr::Match { range, .. }
            | Expr::IfThenElse { range, .. } | Expr::LetTuple { range, .. }
            | Expr::RefConstructor { range, .. } | Expr::Deref { range, .. }
            | Expr::Assign { range, .. } | Expr::Sequence { range, .. } => range,
        }
    }

    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            Expr::Plus(e1, e2, _) | Expr::Minus(e1, e2, _) | Expr::Times(e1, e2, _)
            | Expr::Eq(e1, e2, _) | Expr::Leq(e1, e2, _) | Expr::Geq(e1, e2, _)
            | Expr::Lt(e1, e2, _) | Expr::Gt(e1, e2, _) => {
                e1.free_vars().union(&e2.free_vars()).cloned().collect()
            }

            Expr::FunAbstraction { formals, body, .. } => {
                let formal_names: HashSet<String> = formals.iter()
                    .map(|f| f.name.clone())
                    .collect();
                body.free_vars().difference(&formal_names).cloned().collect()
            }

            Expr::Var(name, _) => {
                let mut set = HashSet::new();
                set.insert(name.clone());
                set
            }

            Expr::Let { bound_var, bind_to, body, .. } => {
                let mut body_free = body.free_vars();
                body_free.remove(bound_var);
                bind_to.free_vars().union(&body_free).cloned().collect()
            }

            Expr::LetRec { bindings, body, .. } => {
                let bound_names: HashSet<String> = bindings.iter()
                    .map(|(name, _, _)| name.clone())
                    .collect();

                let mut all_free = HashSet::new();
                for (_, _, expr) in bindings {
                    all_free.extend(expr.free_vars().difference(&bound_names).cloned());
                }
                all_free.extend(body.free_vars().difference(&bound_names).cloned());
                all_free
            }

            Expr::Application { fn_expr, args, .. } => {
                let mut all_free = fn_expr.free_vars();
                for arg in args {
                    all_free.extend(arg.free_vars());
                }
                all_free
            }

            Expr::ConstructorApplication { arg, .. } => {
                arg.free_vars()
            }

            Expr::Match { scrutinee, cases, .. } => {
                let mut all_free = scrutinee.free_vars();
                for case in cases {
                    match case {
                        MatchCase::ConstructorCase { arg_var, when_cond, body, .. } => {
                            let mut case_free = body.free_vars();
                            case_free.remove(arg_var);
                            all_free.extend(case_free);
                            if let Some(cond) = when_cond {
                                let mut cond_free = cond.free_vars();
                                cond_free.remove(arg_var);
                                all_free.extend(cond_free);
                            }
                        }
                        MatchCase::CatchAllCase { var_name, when_cond, body, .. } => {
                            let mut case_free = body.free_vars();
                            case_free.remove(var_name);
                            all_free.extend(case_free);
                            if let Some(cond) = when_cond {
                                let mut cond_free = cond.free_vars();
                                cond_free.remove(var_name);
                                all_free.extend(cond_free);
                            }
                        }
                    }
                }
                all_free
            }

            Expr::IfThenElse { cond, then_expr, else_expr, .. } => {
                &(&cond.free_vars() | &then_expr.free_vars()) | &else_expr.free_vars()
            }

            Expr::Int(_, _) => HashSet::new(),

            Expr::Tuple(exprs, _) => {
                let mut all_free = HashSet::new();
                for expr in exprs {
                    all_free.extend(expr.free_vars());
                }
                all_free
            }

            Expr::LetTuple { component_vars, bind_to, body, .. } => {
                let bound_names: HashSet<String> = component_vars.iter().cloned().collect();
                let mut body_free = body.free_vars();
                for name in &bound_names {
                    body_free.remove(name);
                }
                bind_to.free_vars().union(&body_free).cloned().collect()
            }

            Expr::RefConstructor { init, .. } => init.free_vars(),

            Expr::Deref { ref_expr, .. } => ref_expr.free_vars(),

            Expr::Assign { ref_expr, new_val, .. } => {
                ref_expr.free_vars().union(&new_val.free_vars()).cloned().collect()
            }

            Expr::Sequence { first, second, .. } => {
                first.free_vars().union(&second.free_vars()).cloned().collect()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Prog {
    pub typedefs: Vec<Typedef>,
    pub expr: Expr,
}
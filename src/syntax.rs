use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};
use std::ops::Range;
use std::hash::Hash;

use im::HashMap as ImHashMap;

use crate::ident::Ident;

pub type Span = Range<usize>;

pub fn merge_spans(a: &Span, b: &Span) -> Span {
    a.start..b.end
}

pub fn dummy_span() -> Span {
    0..0
}

#[derive(Debug, Clone, PartialEq)]
pub enum Path<Id> {
    /// a lexically-scoped identifier, for a module, type, or term
    RootId{id: Id, span: Span},
    /// projection of a field out of the module named by `prefix`
    Select{prefix: Box<Path<Id>>, field: String, span: Span}
}

impl Path<Ident> {
    /// Replaces a path's lexical identifiers with stamped identifiers. `root_desc` names
    /// what the path's root denotes, and appears in the error reported when it is unbound;
    /// the prefix of a projection always denotes a module, whatever the whole path denotes
    pub fn stamp_ids(path: &Path<String>, ctxt: &ImHashMap<String, Ident>, root_desc: &str)
        -> Result<Path<Ident>, (String, Span)>
    {
        match path {
            Path::RootId { id, span } => {
                let ident = ctxt.get(id).ok_or_else(|| {
                    (format!("unbound {} identifier: {}", root_desc, id), span.clone())
                })?;
                Ok(Path::RootId {
                    id: ident.clone(),
                    span: span.clone(),
                })
            },
            Path::Select { prefix, field, span } => Ok(Path::Select {
                prefix: Box::new(Path::stamp_ids(prefix, ctxt, "module")?),
                field: field.clone(),
                span: span.clone(),
            }),
        }
    }


}

impl<Id> Path<Id> {
    pub fn span(&self) -> &Span {
        match self {
            Path::RootId { span, .. } | Path::Select { span, .. } => span,
        }
    }
}

impl<Id: Eq> Path<Id> {

    /// Path equality that ignores spans
    pub fn is_equal(&self, other: &Path<Id>) -> bool {
        match (self, other) {
            (Path::RootId { id: id_a, .. }, Path::RootId { id: id_b, .. }) => {
                id_a == id_b
            }
            (Path::Select { prefix: prefix_a, field: field_a, .. },
             Path::Select { prefix: prefix_b, field: field_b, .. }) => {
                field_a == field_b && prefix_a.is_equal(prefix_b)
            }
            _ => false,
        }
    }
}

impl<Id: Display> fmt::Display for Path<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Path::RootId { id, .. } => write!(f, "{}", id),
            Path::Select { prefix, field, .. } => write!(f, "{}.{}", prefix, field),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant<Id> {
    pub constructor_name: String,
    pub fields: Vec<(String, Ty<Id>, Span)>
}

/// What a single module component declares. Mirrors the `FieldDef` variants of the
/// module it came from
#[derive(Debug, Clone, PartialEq)]
pub enum SigComponent {
    /// a type declaration or, if the kind is a singleton, a defintion
    Ty { kind: Kind<Ident> },
    /// a term declaration, its type, and its index in the module's runtime vector
    Val { ty: Ty<Ident>, index: u16 },
    /// a submodule, its signature, and its index in the enclosing module's runtime vector
    Mod { sig: Signature, index: u16 },
    /// a signature definition, which like a type declaration has no runtime content
    Sig { sig: Signature },
}

/// The components a module exports, as a telescope: each component may refer to those
/// preceding it
#[derive(Debug, Clone, PartialEq)]
pub struct Signature {
    /// the exported components, in declaration order
    pub components: Vec<(String, SigComponent)>,
}

impl Signature {
    /// Looks up the last component whose name matches `field`
    pub fn lookup(&self, field: &str) -> Option<&SigComponent> {
        self.components.iter()
            .rev()
            .find(|(name, _)| name == field)
            .map(|(_, component)| component)
    }

    /// Get the type and runtime slot index of a term component
    pub fn lookup_val_layout(&self, field: &str) -> Option<(&Ty<Ident>, u16)> {
        match self.lookup(field)? {
            SigComponent::Val { ty, index } => Some((ty, *index)),
            _ => None,
        }
    }

    /// Get the signature and runtime slot index of a submodule component
    pub fn lookup_mod_layout(&self, field: &str) -> Option<(&Signature, u16)> {
        match self.lookup(field)? {
            SigComponent::Mod { sig, index } => Some((sig, *index)),
            _ => None,
        }
    }

    /// Get the signature denoted by a signature definition component
    pub fn lookup_sig(&self, field: &str) -> Option<&Signature> {
        match self.lookup(field)? {
            SigComponent::Sig { sig } => Some(sig),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ty<Id> {
    IntTy(Span),
    FunTy { dom: Box<Ty<Id>>, cod: Box<Ty<Id>>, span: Span },
    ProdTy { components: Vec<Ty<Id>>, span: Span },
    RefTy { contained_ty: Box<Ty<Id>>, span: Span },
    SumTy {
        /// Maps each constructor name to its vec of fields
        variants: HashMap<String, Vec<(String, Ty<Id>)>>,
        /// An ordering of all constructor names
        variant_name_ord : Vec<String>,
        range: Span
    },
    /// a type identifier that refers to a type defined in a module
    IdTy { path: Path<Id>, span: Span },
    /// a parameter to a type function, e.g. 'a
    VarTy { name: Id, span: Span },
    TyFunTy { dom: Vec<Id>, cod:Box<Ty<Id>>, span: Span },
    TyAppTy { args: Vec<Box<Ty<Id>>>, ty_fn: Box<Ty<Id>>, span: Span  }
}

impl<Id> Ty<Id> {
    pub fn span(&self) -> &Span {
        match self {
            Ty::IntTy(span) => span,
            Ty::FunTy { span, .. } | Ty::ProdTy { span, .. } | Ty::RefTy { span, .. }
            | Ty::IdTy { span, .. } | Ty::VarTy { span, .. } | Ty::TyFunTy { span, .. }
            | Ty::TyAppTy { span, .. } => span,
            Ty::SumTy { range, .. } => range,
        }
    }
}

impl Ty<Ident> {
    pub fn stamp_ids(ty: &Ty<String>, ctxt: &ImHashMap<String, Ident>) -> Result<Ty<Ident>, (String, Span)> {
        match ty {
            Ty::IntTy(span) => Ok(Ty::IntTy(span.clone())),
            Ty::FunTy { dom, cod, span } => Ok(Ty::FunTy {
                dom: Box::new(Ty::stamp_ids(dom, ctxt)?),
                cod: Box::new(Ty::stamp_ids(cod, ctxt)?),
                span: span.clone(),
            }),
            Ty::ProdTy { components, span } => Ok(Ty::ProdTy {
                components: components.iter()
                    .map(|c| Ty::stamp_ids(c, ctxt))
                    .collect::<Result<Vec<_>, _>>()?,
                span: span.clone(),
            }),
            Ty::RefTy { contained_ty, span } => Ok(Ty::RefTy {
                contained_ty: Box::new(Ty::stamp_ids(contained_ty, ctxt)?),
                span: span.clone(),
            }),
            Ty::SumTy { variants, variant_name_ord, range } => {
                let new_variants = variants.iter().map(|(name, fields)| {
                    let new_fields: Result<Vec<_>, _> = fields.iter().map(|(fname, fty)| {
                        Ok((fname.clone(), Ty::stamp_ids(fty, ctxt)?))
                    }).collect();
                    Ok((name.clone(), new_fields?))
                }).collect::<Result<HashMap<_, _>, (String, Span)>>()?;
                Ok(Ty::SumTy {
                    variants: new_variants,
                    variant_name_ord: variant_name_ord.clone(),
                    range: range.clone(),
                })
            },
            Ty::IdTy { path, span } => {
                Ok(Ty::IdTy {
                    path: Path::stamp_ids(path, ctxt, "type")?,
                    span: span.clone(),
                })
            },
            Ty::VarTy { name, span } => {
                let ident = ctxt.get(name)
                    .ok_or_else(|| (format!("unbound type variable: {}", name), span.clone()))?;
                Ok(Ty::VarTy {
                    name: ident.clone(),
                    span: span.clone()
                })
            },
            Ty::TyFunTy { dom, cod, span } => {
                let mut extended_ctxt = ctxt.clone();
                let new_dom: Vec<Ident> = dom.iter().map(|name| {
                    let ident = Ident::new(name.clone());
                    extended_ctxt.insert(name.clone(), ident.clone());
                    ident
                }).collect();
                Ok(Ty::TyFunTy {
                    dom: new_dom,
                    cod: Box::new(Ty::stamp_ids(cod, &extended_ctxt)?),
                    span: span.clone(),
                })
            },
            Ty::TyAppTy { args, ty_fn, span } => Ok(Ty::TyAppTy {
                args: args.iter()
                    .map(|a| Ok(Box::new(Ty::stamp_ids(a, ctxt)?)))
                    .collect::<Result<Vec<_>, (String, Span)>>()?,
                ty_fn: Box::new(Ty::stamp_ids(ty_fn, ctxt)?),
                span: span.clone(),
            }),
        }
    }
}

/// Kinds classify types
#[derive(Debug, Clone, PartialEq)]
pub enum Kind<Id> {
    /// the kind of proper types whose definition is not known here
    Star { span: Span },
    /// S(ty), the kind inhabited only by types equivalent to `ty`; a transparent
    /// type definition is recorded with this kind
    Singleton { ty: Box<Ty<Id>>, span: Span },
    /// the kind of a type function
    Arrow { dom: Vec<Kind<Id>>, cod: Box<Kind<Id>>, span: Span },
}

impl<Id> Kind<Id> {
    pub fn span(&self) -> &Span {
        match self {
            Kind::Star { span } | Kind::Singleton { span, .. } | Kind::Arrow { span, .. } => span,
        }
    }
}

impl Kind<Ident> {
    pub fn stamp_ids(kind: &Kind<String>, ctxt: &ImHashMap<String, Ident>) -> Result<Kind<Ident>, (String, Span)> {
        match kind {
            Kind::Star { span } => Ok(Kind::Star { span: span.clone() }),
            Kind::Singleton { ty, span } => Ok(Kind::Singleton {
                ty: Box::new(Ty::stamp_ids(ty, ctxt)?),
                span: span.clone(),
            }),
            Kind::Arrow { dom, cod, span } => Ok(Kind::Arrow {
                dom: dom.iter()
                    .map(|k| Kind::stamp_ids(k, ctxt))
                    .collect::<Result<Vec<_>, (String, Span)>>()?,
                cod: Box::new(Kind::stamp_ids(cod, ctxt)?),
                span: span.clone(),
            }),
        }
    }
}

impl<Id: Display> fmt::Display for Kind<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Star { .. } => write!(f, "*"),
            Kind::Singleton { ty, .. } => write!(f, "S({})", ty),
            Kind::Arrow { dom, cod, .. } => {
                let dom_strs: Vec<String> = dom.iter().map(|k| k.to_string()).collect();
                write!(f, "({}) -> {}", dom_strs.join(", "), cod)
            }
        }
    }
}

impl<Id: Eq + Hash + Clone> Ty<Id> {

    /// Type equality that ignores spans
    pub fn is_equal(&self, other: &Ty<Id>) -> bool {
        self.alpha_equal(other, &HashMap::new())
    }

    /// Checks alpha equivalence under a renaming of type variables from self to other
    fn alpha_equal(&self, other: &Ty<Id>, renaming: &HashMap<&Id, &Id>) -> bool {
        match (self, other) {
            (Ty::IntTy(_), Ty::IntTy(_)) => true,
            (Ty::FunTy { dom: dom_a, cod: cod_a, .. }, Ty::FunTy { dom: dom_b, cod: cod_b, .. }) => {
                dom_a.alpha_equal(dom_b, renaming) && cod_a.alpha_equal(cod_b, renaming)
            }
            (Ty::ProdTy { components: comp_a, .. }, Ty::ProdTy { components: comp_b, .. }) => {
                comp_a.len() == comp_b.len() &&
                comp_a.iter().zip(comp_b.iter()).all(|(a, b)| a.alpha_equal(b, renaming))
            }
            (Ty::RefTy { contained_ty: ty_a, .. }, Ty::RefTy { contained_ty: ty_b, .. }) => {
                ty_a.alpha_equal(ty_b, renaming)
            }
            (Ty::SumTy { variants: var_a, .. }, Ty::SumTy { variants: var_b, .. }) => {
                var_a.len() == var_b.len() &&
                var_a.iter().all(|(name, fields_a)| {
                    var_b.get(name).map_or(false, |fields_b| {
                        fields_a.len() == fields_b.len() &&
                        fields_a.iter().zip(fields_b.iter()).all(|((name_a, ty_a), (name_b, ty_b))| {
                            name_a == name_b && ty_a.alpha_equal(ty_b, renaming)
                        })
                    })
                })
            }
            (Ty::IdTy { path:path_a, ..}, Ty::IdTy { path:path_b, ..}) => {
                path_a.is_equal(path_b)
            }
            (Ty::VarTy { name: name_a, .. }, Ty::VarTy { name: name_b, .. }) => {
                match renaming.get(&name_a) {
                    Some(&renamed) => *renamed == *name_b,
                    None => *name_a == *name_b,
                }
            }
            (Ty::TyAppTy { args: args_a, ty_fn: fn_a, .. }, Ty::TyAppTy { args: args_b, ty_fn: fn_b, .. }) => {
                args_a.len() == args_b.len() &&
                fn_a.alpha_equal(fn_b, renaming) &&
                args_a.iter().zip(args_b.iter()).all(|(a, b)| a.alpha_equal(b, renaming))
            }
            (Ty::TyFunTy { dom: dom_a, cod: cod_a, .. }, Ty::TyFunTy { dom: dom_b, cod: cod_b, .. }) => {
                dom_a.len() == dom_b.len() && {
                    let mut extended = renaming.clone();
                    for (a, b) in dom_a.iter().zip(dom_b.iter()) {
                        extended.insert(a, b);
                    }
                    cod_a.alpha_equal(cod_b, &extended)
                }
            }
            _ => false,
        }
    }

    /// Returns a list of the types of a function type's domain
    pub fn dom_ty_list(&self) -> Vec<Ty<Id>> {
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
    pub fn apply(&self, n: usize) -> Ty<Id> {
        match (n, self) {
            (0, _) => self.clone(),
            (_, Ty::FunTy { cod, .. }) => cod.apply(n - 1),
            _ => panic!("applied function type to too many args"),
        }
    }
}

impl<Id: Display> fmt::Display for Ty<Id> {
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
            Ty::IdTy { path, .. } => write!(f, "{}", path),
            Ty::VarTy { name, .. } => write!(f, "{}", name),
            Ty::TyFunTy { dom, cod, .. } => {
                let formal_names : Vec<String> = dom.iter().map(|d| d.to_string()).collect();
                write!(f, "({}) {}", formal_names.join(", "), cod)
            },
            Ty::TyAppTy { args, ty_fn, .. } => {
                let arg_strs: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "{} [{}]", ty_fn, arg_strs.join(", "))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SumTypeDef<Id> {
    pub typename: Id,
    pub variants: Vec<Variant<Id>>,
    pub span: Span,
}

impl SumTypeDef<Ident> {
    pub fn stamp_ids(def: &SumTypeDef<String>, ctxt: &ImHashMap<String, Ident>) -> Result<SumTypeDef<Ident>, (String, Span)> {
        let ident = ctxt.get(&def.typename)
            .ok_or_else(|| (format!("unbound type name: {}", def.typename), def.span.clone()))?;
        let new_variants = def.variants.iter().map(|v| {
            let new_fields = v.fields.iter().map(|(fname, ty, fspan)| {
                Ok((fname.clone(), Ty::stamp_ids(ty, ctxt)?, fspan.clone()))
            }).collect::<Result<Vec<_>, (String, Span)>>()?;
            Ok(Variant {
                constructor_name: v.constructor_name.clone(),
                fields: new_fields,
            })
        }).collect::<Result<Vec<_>, (String, Span)>>()?;
        Ok(SumTypeDef {
            typename: ident.clone(),
            variants: new_variants,
            span: def.span.clone(),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Formal<Id> {
    pub name: Id,
    pub ty: Ty<Id>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchCase<Id> {
    pub pat: Pattern<Id>,
    pub when_cond: Option<Box<Expr<Id>>>,
    pub body: Box<Expr<Id>>,
    pub span: Span
}

impl<Id> MatchCase<Id> {
    /// If this case has an outer-level ConstructorApplication pattern then return
    /// Some(n), where n is the constructor name as a string. Otherwise, return None.
    pub fn get_variant_id(&self) -> Option<String> {
        match &self.pat {
            Pattern::ConstructorApplication { name, .. } => {
                Some(name.clone())
            },
            _ => {
                None
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern<Id> {
    Var(Id, Span),
    ConstructorApplication{
        name: String,
        fields: HashMap<String, (Box<Pattern<Id>>, Span)>,
        /// Are missing fields allowed?
        open: bool,
        span: Span

    },
    Int(i32, Span),
    Tuple(Vec<Pattern<Id>>, Span)
}

impl Pattern<Ident> {
    /// Converts a Pattern<String> to a Pattern<Ident>, creating fresh stamps for
    /// each variable binding. Returns the converted pattern and an extended context.
    pub fn stamp_ids(
        pat: &Pattern<String>,
        ctxt: &ImHashMap<String, Ident>,
    ) -> Result<(Pattern<Ident>, ImHashMap<String, Ident>), (String, Span)> {
        match pat {
            Pattern::Var(name, span) => {
                let ident = Ident::new(name.clone());
                let new_ctxt = ctxt.update(name.clone(), ident.clone());
                Ok((Pattern::Var(ident, span.clone()), new_ctxt))
            }
            Pattern::Int(n, span) => Ok((Pattern::Int(*n, span.clone()), ctxt.clone())),
            Pattern::Tuple(pats, span) => {
                let mut cur_ctxt = ctxt.clone();
                let mut new_pats = Vec::new();
                for p in pats {
                    let (new_pat, next_ctxt) = Pattern::stamp_ids(p, &cur_ctxt)?;
                    new_pats.push(new_pat);
                    cur_ctxt = next_ctxt;
                }
                Ok((Pattern::Tuple(new_pats, span.clone()), cur_ctxt))
            }
            Pattern::ConstructorApplication { name, fields, open, span } => {
                let mut cur_ctxt = ctxt.clone();
                let mut new_fields = HashMap::new();
                for (fname, (pat, fspan)) in fields {
                    let (new_pat, next_ctxt) = Pattern::stamp_ids(pat, &cur_ctxt)?;
                    new_fields.insert(fname.clone(), (Box::new(new_pat), fspan.clone()));
                    cur_ctxt = next_ctxt;
                }
                Ok((Pattern::ConstructorApplication {
                    name: name.clone(),
                    fields: new_fields,
                    open: *open,
                    span: span.clone(),
                }, cur_ctxt))
            }
        }
    }
}

impl<Id: Hash + Clone + Eq> Pattern<Id> {
    pub fn bound_vars(&self) -> HashSet<Id> {
        match self {
            Pattern::Var(name, _) => {
                let mut set = HashSet::new();
                set.insert(name.clone());
                set
            },
            Pattern::Int(_, _) => HashSet::new(),
            Pattern::Tuple(pats, _) => {
                pats.iter().flat_map(|p| p.bound_vars()).collect()
            },
            Pattern::ConstructorApplication { fields, .. } => {
                fields.values().flat_map(|p| p.0.bound_vars()).collect()
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<Id> {
    Plus(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Minus(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Times(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Eq(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Leq(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Geq(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Lt(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    Gt(Box<Expr<Id>>, Box<Expr<Id>>, Span),
    FunAbstraction {
        formals: Vec<Formal<Id>>,
        body: Box<Expr<Id>>,
        span: Span,
    },
    Var(Id, Span),
    ValPath { path: Path<Id>, span: Span },
    Let {
        bound_pat: Box<Pattern<Id>>,
        bind_to: Box<Expr<Id>>,
        body: Box<Expr<Id>>,
        span: Span,
    },
    LetRec {
        bindings: Vec<(Id, Ty<Id>, Expr<Id>)>,
        body: Box<Expr<Id>>,
        span: Span,
    },
    Application {
        fn_expr: Box<Expr<Id>>,
        args: Vec<Expr<Id>>,
        span: Span,
    },
    ConstructorApplication {
        name: String,
        fields: Vec<(String, Box<Expr<Id>>, Span)>,
        span: Span,
    },
    Match {
        scrutinee: Box<Expr<Id>>,
        cases: Vec<MatchCase<Id>>,
        span: Span,
    },
    IfThenElse {
        cond: Box<Expr<Id>>,
        then_expr: Box<Expr<Id>>,
        else_expr: Box<Expr<Id>>,
        span: Span,
    },
    Int(i32, Span),
    Tuple(Vec<Expr<Id>>, Span),
    RefConstructor {
        init: Box<Expr<Id>>,
        span: Span,
    },
    Deref {
        ref_expr: Box<Expr<Id>>,
        span: Span,
    },
    Assign {
        ref_expr: Box<Expr<Id>>,
        new_val: Box<Expr<Id>>,
        span: Span,
    },
    Sequence {
        first: Box<Expr<Id>>,
        second: Box<Expr<Id>>,
        span: Span,
    },
}

impl Expr<Ident> {
    pub fn stamp_ids(
        expr: &Expr<String>,
        ctxt: &ImHashMap<String, Ident>,
    ) -> Result<Expr<Ident>, (String, Span)> {
        let conv = |e: &Expr<String>| Expr::stamp_ids(e, ctxt);
        let conv_ty = |t: &Ty<String>| Ty::stamp_ids(t, ctxt);
        match expr {
            Expr::Plus(e1, e2, span) => Ok(Expr::Plus(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Minus(e1, e2, span) => Ok(Expr::Minus(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Times(e1, e2, span) => Ok(Expr::Times(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Eq(e1, e2, span) => Ok(Expr::Eq(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Leq(e1, e2, span) => Ok(Expr::Leq(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Geq(e1, e2, span) => Ok(Expr::Geq(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Lt(e1, e2, span) => Ok(Expr::Lt(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Gt(e1, e2, span) => Ok(Expr::Gt(Box::new(conv(e1)?), Box::new(conv(e2)?), span.clone())),
            Expr::Var(name, span) => {
                let ident = ctxt.get(name)
                    .ok_or_else(|| (format!("unbound variable: {}", name), span.clone()))?;
                Ok(Expr::Var(ident.clone(), span.clone()))
            }
            Expr::ValPath { path, span } => Ok(Expr::ValPath {
                path: Path::stamp_ids(path, ctxt, "value")?,
                span: span.clone(),
            }),
            Expr::Int(n, span) => Ok(Expr::Int(*n, span.clone())),
            Expr::Tuple(exprs, span) => {
                let new_exprs = exprs.iter().map(|e| conv(e)).collect::<Result<Vec<_>, _>>()?;
                Ok(Expr::Tuple(new_exprs, span.clone()))
            }
            Expr::FunAbstraction { formals, body, span } => {
                let mut body_ctxt = ctxt.clone();
                let new_formals: Vec<Formal<Ident>> = formals.iter().map(|f| {
                    let ident = Ident::new(f.name.clone());
                    body_ctxt.insert(f.name.clone(), ident.clone());
                    Ok(Formal { name: ident, ty: conv_ty(&f.ty)? })
                }).collect::<Result<Vec<_>, (String, Span)>>()?;
                let new_body = Expr::stamp_ids(body, &body_ctxt)?;
                Ok(Expr::FunAbstraction {
                    formals: new_formals,
                    body: Box::new(new_body),
                    span: span.clone(),
                })
            }
            Expr::Let { bound_pat, bind_to, body, span } => {
                let new_bind_to = conv(bind_to)?;
                let (new_pat, body_ctxt) = Pattern::stamp_ids(bound_pat, ctxt)?;
                let new_body = Expr::stamp_ids(body, &body_ctxt)?;
                Ok(Expr::Let {
                    bound_pat: Box::new(new_pat),
                    bind_to: Box::new(new_bind_to),
                    body: Box::new(new_body),
                    span: span.clone(),
                })
            }
            Expr::LetRec { bindings, body, span } => {
                let mut rec_ctxt = ctxt.clone();
                let idents: Vec<Ident> = bindings.iter().map(|(name, _, _)| {
                    let ident = Ident::new(name.clone());
                    rec_ctxt.insert(name.clone(), ident.clone());
                    ident
                }).collect();
                let new_bindings = idents.into_iter().zip(bindings.iter()).map(|(ident, (_, ty, expr))| {
                    let new_ty = Ty::stamp_ids(ty, &rec_ctxt)?;
                    let new_expr = Expr::stamp_ids(expr, &rec_ctxt)?;
                    Ok((ident, new_ty, new_expr))
                }).collect::<Result<Vec<_>, (String, Span)>>()?;
                let new_body = Expr::stamp_ids(body, &rec_ctxt)?;
                Ok(Expr::LetRec {
                    bindings: new_bindings,
                    body: Box::new(new_body),
                    span: span.clone(),
                })
            }
            Expr::Application { fn_expr, args, span } => {
                let new_fn = conv(fn_expr)?;
                let new_args = args.iter().map(|a| conv(a)).collect::<Result<Vec<_>, _>>()?;
                Ok(Expr::Application {
                    fn_expr: Box::new(new_fn),
                    args: new_args,
                    span: span.clone(),
                })
            }
            Expr::ConstructorApplication { name, fields, span } => {
                let new_fields = fields.iter().map(|(fname, expr, fspan)| {
                    Ok((fname.clone(), Box::new(conv(expr)?), fspan.clone()))
                }).collect::<Result<Vec<_>, (String, Span)>>()?;
                Ok(Expr::ConstructorApplication {
                    name: name.clone(),
                    fields: new_fields,
                    span: span.clone(),
                })
            }
            Expr::Match { scrutinee, cases, span } => {
                let new_scrutinee = conv(scrutinee)?;
                let new_cases = cases.iter().map(|case| {
                    let (new_pat, case_ctxt) = Pattern::stamp_ids(&case.pat, ctxt)?;
                    let new_when_cond = match &case.when_cond {
                        Some(cond) => Some(Box::new(Expr::stamp_ids(cond, &case_ctxt)?)),
                        None => None,
                    };
                    let new_body = Expr::stamp_ids(&case.body, &case_ctxt)?;
                    Ok(MatchCase {
                        pat: new_pat,
                        when_cond: new_when_cond,
                        body: Box::new(new_body),
                        span: case.span.clone(),
                    })
                }).collect::<Result<Vec<_>, (String, Span)>>()?;
                Ok(Expr::Match {
                    scrutinee: Box::new(new_scrutinee),
                    cases: new_cases,
                    span: span.clone(),
                })
            }
            Expr::IfThenElse { cond, then_expr, else_expr, span } => Ok(Expr::IfThenElse {
                cond: Box::new(conv(cond)?),
                then_expr: Box::new(conv(then_expr)?),
                else_expr: Box::new(conv(else_expr)?),
                span: span.clone(),
            }),
            Expr::RefConstructor { init, span } => Ok(Expr::RefConstructor {
                init: Box::new(conv(init)?),
                span: span.clone(),
            }),
            Expr::Deref { ref_expr, span } => Ok(Expr::Deref {
                ref_expr: Box::new(conv(ref_expr)?),
                span: span.clone(),
            }),
            Expr::Assign { ref_expr, new_val, span } => Ok(Expr::Assign {
                ref_expr: Box::new(conv(ref_expr)?),
                new_val: Box::new(conv(new_val)?),
                span: span.clone(),
            }),
            Expr::Sequence { first, second, span } => Ok(Expr::Sequence {
                first: Box::new(conv(first)?),
                second: Box::new(conv(second)?),
                span: span.clone(),
            }),
        }
    }
}

impl<Id: Clone + Hash + Eq> Expr<Id> {
    pub fn span(&self) -> &Span {
        match self {
            Expr::Plus(_, _, span) | Expr::Minus(_, _, span) | Expr::Times(_, _, span)
            | Expr::Eq(_, _, span) | Expr::Leq(_, _, span) | Expr::Geq(_, _, span)
            | Expr::Lt(_, _, span) | Expr::Gt(_, _, span) | Expr::Var(_, span)
            | Expr::Int(_, span) | Expr::Tuple(_, span) => span,
            Expr::ValPath { span, .. }
            | Expr::FunAbstraction { span, .. } | Expr::Let { span, .. }
            | Expr::LetRec { span, .. } | Expr::Application { span, .. }
            | Expr::ConstructorApplication { span, .. } | Expr::Match { span, .. }
            | Expr::IfThenElse { span, .. }
            | Expr::RefConstructor { span, .. } | Expr::Deref { span, .. }
            | Expr::Assign { span, .. } | Expr::Sequence { span, .. } => span,
        }
    }

    pub fn with_span(mut self, new_span: Span) -> Self {
        match &mut self {
            Expr::Plus(_, _, span) | Expr::Minus(_, _, span) | Expr::Times(_, _, span)
            | Expr::Eq(_, _, span) | Expr::Leq(_, _, span) | Expr::Geq(_, _, span)
            | Expr::Lt(_, _, span) | Expr::Gt(_, _, span) | Expr::Var(_, span)
            | Expr::Int(_, span) | Expr::Tuple(_, span) => *span = new_span,
            Expr::ValPath { span, .. }
            | Expr::FunAbstraction { span, .. } | Expr::Let { span, .. }
            | Expr::LetRec { span, .. } | Expr::Application { span, .. }
            | Expr::ConstructorApplication { span, .. } | Expr::Match { span, .. }
            | Expr::IfThenElse { span, .. }
            | Expr::RefConstructor { span, .. } | Expr::Deref { span, .. }
            | Expr::Assign { span, .. } | Expr::Sequence { span, .. } => *span = new_span,
        }
        self
    }

    pub fn free_vars(&self) -> HashSet<Id> {
        match self {
            Expr::Plus(e1, e2, _) | Expr::Minus(e1, e2, _) | Expr::Times(e1, e2, _)
            | Expr::Eq(e1, e2, _) | Expr::Leq(e1, e2, _) | Expr::Geq(e1, e2, _)
            | Expr::Lt(e1, e2, _) | Expr::Gt(e1, e2, _) => {
                e1.free_vars().union(&e2.free_vars()).cloned().collect()
            }

            Expr::FunAbstraction { formals, body, .. } => {
                let formal_names: HashSet<Id> = formals.iter()
                    .map(|f| f.name.clone())
                    .collect();
                body.free_vars().difference(&formal_names).cloned().collect()
            }

            Expr::Var(name, _) => {
                let mut set = HashSet::new();
                set.insert(name.clone());
                set
            }

            Expr::ValPath { .. } => HashSet::new(),

            Expr::Let { bound_pat, bind_to, body, .. } => {
                let body_free = body.free_vars()
                    .difference(&bound_pat.bound_vars())
                    .cloned()
                    .collect();
                bind_to.free_vars().union(&body_free).cloned().collect()
            }

            Expr::LetRec { bindings, body, .. } => {
                let bound_names: HashSet<Id> = bindings.iter()
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

            Expr::ConstructorApplication { fields, .. } => {
                let mut all_free = HashSet::new();
                for (_, expr, _) in fields {
                    all_free.extend(expr.free_vars());
                }
                all_free
            }

            Expr::Match { scrutinee, cases, .. } => {
                let mut all_free = scrutinee.free_vars();
                for case in cases {
                    let MatchCase { pat, when_cond, body, .. } = case;
                    let mut case_free = body.free_vars();
                    if let Some(cond) = when_cond {
                        case_free.extend(cond.free_vars());
                    }
                    all_free.extend(case_free.difference(&pat.bound_vars()).cloned());
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
pub struct Prog<Id> {
    pub fields: Vec<FieldDef<Id>>,
    pub span: Span,
}

/// A single binding in a module.
#[derive(Debug, Clone, PartialEq)]
pub enum FieldDef<Id> {
    /// a value definition, e.g. `val x = 3`
    ValDef{id: Id, expr: Expr<Id>, span: Span},
    /// a transparent type definition, e.g. `type t = int`
    TyDef{id: Id, ty: Ty<Id>, span: Span},
    /// a discriminated union definition, which also brings its constructors into scope
    SumTypeDef{def: SumTypeDef<Id>},
    /// a submodule definition, e.g. `module M = struct ... end`
    ModDef{id: Id, module: ModuleTerm<Id>, span: Span},
    /// a module signature definition
    SigDef{id: Id, sig: SigExpr<Id>, span: Span}
}

/// A component declared in a signature, as written in source
#[derive(Debug, Clone, PartialEq)]
pub enum SigDecl<Id> {
    /// `type t` when the kind is `Star`, or `type t = ty` when it is a singleton
    TyDecl{id: Id, kind: Kind<Id>, span: Span},
    /// a value declaration, e.g. `val x : int`
    ValDecl{id: Id, ty: Ty<Id>, span: Span},
    /// a submodule declaration, e.g. `module M : sig ... end`
    ModDecl{id: Id, sig: SigExpr<Id>, span: Span},
    /// a signature definition, e.g. `signature S = sig ... end`
    SigDecl{id: Id, sig: SigExpr<Id>, span: Span},
}

impl<Id> SigDecl<Id> {
    pub fn span(&self) -> &Span {
        match self {
            SigDecl::TyDecl { span, .. } | SigDecl::ValDecl { span, .. }
            | SigDecl::ModDecl { span, .. } | SigDecl::SigDecl { span, .. } => span,
        }
    }
}

/// A signature as written in source, before elaboration into a `Signature`
#[derive(Debug, Clone, PartialEq)]
pub enum SigExpr<Id> {
    /// a literal signature, written `sig ... end`, whose declarations are scoped
    /// positionally in the same way a module's components are
    Sig{decls: Vec<SigDecl<Id>>, span: Span},
    /// a reference to a signature bound by an earlier definition
    SigPath{path: Path<Id>, span: Span},
}

impl<Id> SigExpr<Id> {
    pub fn span(&self) -> &Span {
        match self {
            SigExpr::Sig { span, .. } | SigExpr::SigPath { span, .. } => span,
        }
    }
}

impl SigExpr<Ident> {
    /// Stamps a signature's declarations in order, threading the context forward so that
    /// each declaration is stamped under the type names its predecessors introduce
    pub fn stamp_ids(sig: &SigExpr<String>, ctxt: &ImHashMap<String, Ident>)
        -> Result<SigExpr<Ident>, (String, Span)>
    {
        match sig {
            SigExpr::SigPath { path, span } => Ok(SigExpr::SigPath {
                path: Path::stamp_ids(path, ctxt, "signature")?,
                span: span.clone(),
            }),
            SigExpr::Sig { decls, span } => {
                let mut inner_ctxt = ctxt.clone();
                let mut new_decls = Vec::new();
                for decl in decls {
                    new_decls.push(SigDecl::stamp_ids(decl, &mut inner_ctxt)?);
                }
                Ok(SigExpr::Sig { decls: new_decls, span: span.clone() })
            }
        }
    }
}

impl SigDecl<Ident> {
    /// Stamps one declaration, extending `ctxt` with the identifier it binds so that
    /// subsequent declarations in the same signature can refer to it
    pub fn stamp_ids(decl: &SigDecl<String>, ctxt: &mut ImHashMap<String, Ident>)
        -> Result<SigDecl<Ident>, (String, Span)>
    {
        match decl {
            SigDecl::TyDecl { id, kind, span } => {
                let new_kind = Kind::stamp_ids(kind, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(SigDecl::TyDecl { id: ident, kind: new_kind, span: span.clone() })
            },
            SigDecl::ValDecl { id, ty, span } => {
                let new_ty = Ty::stamp_ids(ty, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(SigDecl::ValDecl { id: ident, ty: new_ty, span: span.clone() })
            },
            SigDecl::ModDecl { id, sig, span } => {
                let new_sig = SigExpr::stamp_ids(sig, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(SigDecl::ModDecl { id: ident, sig: new_sig, span: span.clone() })
            },
            SigDecl::SigDecl { id, sig, span } => {
                let new_sig = SigExpr::stamp_ids(sig, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(SigDecl::SigDecl { id: ident, sig: new_sig, span: span.clone() })
            }
        }
    }
}

impl<Id> FieldDef<Id> {
    pub fn span(&self) -> &Span {
        match self {
            FieldDef::ValDef { span, .. } | FieldDef::TyDef { span, .. }
            | FieldDef::ModDef { span, .. } | FieldDef::SigDef { span, .. } => span,
            FieldDef::SumTypeDef { def } => &def.span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ModuleTerm<Id> {
    /// a literal module, written `mod ... end`, whose components are scoped positionally
    Mod{fields: Vec<FieldDef<Id>>, span: Span},
    /// a reference to a module already in scope, possibly projected from another module
    ModulePath{path: Path<Id>, span: Span}
}

impl<Id> ModuleTerm<Id> {
    pub fn span(&self) -> &Span {
        match self {
            ModuleTerm::Mod { span, .. } | ModuleTerm::ModulePath { span, .. } => span,
        }
    }
}

impl ModuleTerm<Ident> {
    pub fn stamp_ids(module: &ModuleTerm<String>, ctxt: &ImHashMap<String, Ident>)
        -> Result<ModuleTerm<Ident>, (String, Span)>
    {
        match module {
            ModuleTerm::ModulePath { path, span } => Ok(ModuleTerm::ModulePath {
                path: Path::stamp_ids(path, ctxt, "module")?,
                span: span.clone(),
            }),
            ModuleTerm::Mod { fields, span } => {
                let mut inner_ctxt = ctxt.clone();
                let mut new_fields = Vec::new();
                for field in fields {
                    new_fields.push(FieldDef::stamp_ids(field, &mut inner_ctxt)?);
                }
                Ok(ModuleTerm::Mod {
                    fields: new_fields,
                    span: span.clone(),
                })
            }
        }
    }
}

impl FieldDef<Ident> {
    pub fn stamp_ids(field: &FieldDef<String>, ctxt: &mut ImHashMap<String, Ident>)
        -> Result<FieldDef<Ident>, (String, Span)>
    {
        match field {
            FieldDef::ValDef { id, expr, span } => {
                let new_expr = Expr::stamp_ids(expr, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(FieldDef::ValDef { id: ident, expr: new_expr, span: span.clone() })
            },
            FieldDef::TyDef { id, ty, span } => {
                let new_ty = Ty::stamp_ids(ty, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(FieldDef::TyDef { id: ident, ty: new_ty, span: span.clone() })
            },
            FieldDef::SumTypeDef { def } => {
                let ident = Ident::new(def.typename.clone());
                ctxt.insert(def.typename.clone(), ident);
                Ok(FieldDef::SumTypeDef { def: SumTypeDef::stamp_ids(def, ctxt)? })
            },
            FieldDef::ModDef { id, module, span } => {
                let new_module = ModuleTerm::stamp_ids(module, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(FieldDef::ModDef { id: ident, module: new_module, span: span.clone() })
            },
            FieldDef::SigDef { id, sig, span } => {
                let new_sig = SigExpr::stamp_ids(sig, ctxt)?;
                let ident = Ident::new(id.clone());
                ctxt.insert(id.clone(), ident.clone());
                Ok(FieldDef::SigDef { id: ident, sig: new_sig, span: span.clone() })
            }
        }
    }
}

impl Prog<Ident> {
    pub fn stamp_ids(p: &Prog<String>) -> Result<Prog<Ident>, (String, Span)> {
        let mut ctxt = ImHashMap::new();
        let mut new_fields = Vec::new();
        for field in &p.fields {
            new_fields.push(FieldDef::stamp_ids(field, &mut ctxt)?);
        }
        Ok(Prog {
            fields: new_fields,
            span: p.span.clone(),
        })
    }
}
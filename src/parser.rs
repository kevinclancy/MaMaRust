use chumsky::prelude::*;
use crate::syntax::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token {
    // Identifiers and literals
    Id(String),
    Constructor(String),
    Int(i32),
    
    // Delimiters
    LParen,
    RParen,
    LBrack,
    RBrack,
    LSquareBrack,
    RSquareBrack,
    
    // Operators
    Plus,
    Minus,
    Times,
    Eq,
    Leq,
    Geq,
    Lt,
    Gt,
    Bind,
    Assign,
    Bang,
    Pipe,
    
    // Keywords
    Let,
    In,
    Rec,
    Fun,
    If,
    Then,
    Else,
    Match,
    With,
    When,
    Of,
    And,
    Ref,
    Typedef,
    To,
    
    // Punctuation
    Semicolon,
    Comma,
    Colon,
    TypeInt,
}

pub fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let int = text::int(10).map(|s: String| Token::Int(s.parse().unwrap()));
    
    let id = text::ident().map(|s: String| {
        match s.as_str() {
            "let" => Token::Let,
            "in" => Token::In,
            "rec" => Token::Rec,
            "fun" => Token::Fun,
            "if" => Token::If,
            "then" => Token::Then,
            "else" => Token::Else,
            "match" => Token::Match,
            "with" => Token::With,
            "when" => Token::When,
            "of" => Token::Of,
            "and" => Token::And,
            "ref" => Token::Ref,
            "typedef" => Token::Typedef,
            "to" => Token::To,
            "int" => Token::TypeInt,
            _ => {
                if s.chars().next().unwrap().is_uppercase() {
                    Token::Constructor(s)
                } else {
                    Token::Id(s)
                }
            }
        }
    });
    
    let op = choice((
        just("==").to(Token::Eq),
        just("<=").to(Token::Leq),
        just(">=").to(Token::Geq),
        just(":=").to(Token::Assign),
        just("->").to(Token::To),
        just("+").to(Token::Plus),
        just("-").to(Token::Minus),
        just("*").to(Token::Times),
        just("=").to(Token::Bind),
        just("<").to(Token::Lt),
        just(">").to(Token::Gt),
        just("!").to(Token::Bang),
        just("|").to(Token::Pipe),
        just("(").to(Token::LParen),
        just(")").to(Token::RParen),
        just("{").to(Token::LBrack),
        just("}").to(Token::RBrack),
        just("[").to(Token::LSquareBrack),
        just("]").to(Token::RSquareBrack),
        just(";").to(Token::Semicolon),
        just(",").to(Token::Comma),
        just(":").to(Token::Colon),
    ));
    
    let comment = just("//").then(take_until(text::newline())).ignored();
    
    let token = choice((int, id, op)).padded();
    
    token
        .repeated()
        .then_ignore(end())
        .padded_by(comment.repeated())
}

pub fn expr_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    recursive(|expr| {
        let int = select! { Token::Int(n) => Expr::Int(n, Range::dummy()) };
        let var = select! { Token::Id(name) => Expr::Var(name, Range::dummy()) };
        
        // Function abstraction: (fun (param : type) -> expr)
        let fun_abstraction = just(Token::Fun)
            .ignore_then(just(Token::LParen))
            .ignore_then(
                select! { Token::Id(name) => name }
                    .then_ignore(just(Token::Colon))
                    .then(type_parser())
                    .map(|(name, ty)| Formal { name, ty })
                    .separated_by(just(Token::Comma))
            )
            .then_ignore(just(Token::RParen))
            .then_ignore(just(Token::To))
            .then(expr.clone())
            .map(|(formals, body)| Expr::FunAbstraction {
                formals,
                body: Box::new(body),
                range: Range::dummy(),
            });
        
        // Let expression: let x = expr in expr OR let (x,y,z) = expr in expr
        let let_expr = just(Token::Let)
            .ignore_then(choice((
                // Tuple destructuring: let (x,y,z) = expr in expr
                select! { Token::Id(name) => name }
                    .separated_by(just(Token::Comma))
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .then_ignore(just(Token::Bind))
                    .then(expr.clone())
                    .then_ignore(just(Token::In))
                    .then(expr.clone())
                    .map(|((component_vars, bind_to), body)| Expr::LetTuple {
                        component_vars,
                        bind_to: Box::new(bind_to),
                        body: Box::new(body),
                        range: Range::dummy(),
                    }),
                // Simple let: let x = expr in expr
                select! { Token::Id(name) => name }
                    .then_ignore(just(Token::Bind))
                    .then(expr.clone())
                    .then_ignore(just(Token::In))
                    .then(expr.clone())
                    .map(|((bound_var, bind_to), body)| Expr::Let {
                        bound_var,
                        bind_to: Box::new(bind_to),
                        body: Box::new(body),
                        range: Range::dummy(),
                    }),
            )));
        
        // Let rec expression: let rec bindings in expr
        let let_rec = just(Token::Let)
            .ignore_then(just(Token::Rec))
            .ignore_then(
                select! { Token::Id(name) => name }
                    .then_ignore(just(Token::Colon))
                    .then(type_parser())
                    .then_ignore(just(Token::Bind))
                    .then(expr.clone())
                    .map(|((name, ty), expr)| (name, ty, expr))
                    .separated_by(just(Token::And))
            )
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|(bindings, body)| Expr::LetRec {
                bindings,
                body: Box::new(body),
                range: Range::dummy(),
            });
        
        // If-then-else: if expr then expr else expr
        let if_then_else = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Then))
            .then(expr.clone())
            .then_ignore(just(Token::Else))
            .then(expr.clone())
            .map(|((cond, then_expr), else_expr)| Expr::IfThenElse {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
                range: Range::dummy(),
            });
        
        // Match expression: match expr with cases
        let match_case = just(Token::Pipe)
            .ignore_then(choice((
                // Constructor case: | Constructor var when guard -> expr
                select! { Token::Constructor(name) => name }
                    .then(select! { Token::Id(var) => var })
                    .then(just(Token::When).ignore_then(expr.clone()).or_not())
                    .then_ignore(just(Token::To))
                    .then(expr.clone())
                    .map(|(((name, arg_var), when_cond), body)| MatchCase::ConstructorCase {
                        name,
                        arg_var,
                        when_cond: when_cond.map(Box::new),
                        body: Box::new(body),
                        range: Range::dummy(),
                    }),
                // Catch-all case: | var when guard -> expr  
                select! { Token::Id(var_name) => var_name }
                    .then(just(Token::When).ignore_then(expr.clone()).or_not())
                    .then_ignore(just(Token::To))
                    .then(expr.clone())
                    .map(|((var_name, when_cond), body)| MatchCase::CatchAllCase {
                        var_name,
                        when_cond: when_cond.map(Box::new),
                        body: Box::new(body),
                        range: Range::dummy(),
                    }),
            )))
            .recover_with(skip_then_retry_until([Token::Pipe]));
        
        let match_expr = just(Token::Match)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::With))
            .then(match_case.repeated().at_least(1))
            .map(|(scrutinee, cases)| Expr::Match {
                scrutinee: Box::new(scrutinee),
                cases,
                range: Range::dummy(),
            });
        
        // Reference operations
        let ref_constructor = just(Token::Ref)
            .ignore_then(expr.clone())
            .map(|init| Expr::RefConstructor {
                init: Box::new(init),
                range: Range::dummy(),
            });
        
        let deref = just(Token::Bang)
            .ignore_then(expr.clone())
            .map(|ref_expr| Expr::Deref {
                ref_expr: Box::new(ref_expr),
                range: Range::dummy(),
            });
        
        // Constructor application: (Constructor expr)
        let constructor_app = just(Token::LParen)
            .ignore_then(select! { Token::Constructor(name) => name })
            .then(expr.clone())
            .then_ignore(just(Token::RParen))
            .map(|(name, arg)| Expr::ConstructorApplication {
                name,
                arg: Box::new(arg),
                range: Range::dummy(),
            });
        
        // Parenthesized expressions and tuples
        let paren_expr = expr.clone()
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|exprs| {
                match exprs.len() {
                    0 => Expr::Tuple(vec![], Range::dummy()),
                    1 => exprs.into_iter().next().unwrap(),
                    _ => Expr::Tuple(exprs, Range::dummy()),
                }
            });
        
        let atom = choice((
            int,
            var,
            fun_abstraction,
            let_expr,
            let_rec,
            if_then_else,
            match_expr,
            ref_constructor,
            deref,
            constructor_app,
            paren_expr,
        ));
        
        // Function application: (expr exprlist)
        let application = atom.clone()
            .then(
                just(Token::LParen)
                    .ignore_then(expr.clone().separated_by(just(Token::Comma)))
                    .then_ignore(just(Token::RParen))
                    .or_not()
            )
            .map(|(fn_expr, args)| {
                if let Some(args) = args {
                    if !args.is_empty() {
                        Expr::Application {
                            fn_expr: Box::new(fn_expr),
                            args,
                            range: Range::dummy(),
                        }
                    } else {
                        fn_expr
                    }
                } else {
                    fn_expr
                }
            });
        
        // Assignment: expr := expr
        let assignment = application.clone()
            .then(just(Token::Assign).ignore_then(application.clone()).or_not())
            .map(|(ref_expr, new_val)| {
                if let Some(new_val) = new_val {
                    Expr::Assign {
                        ref_expr: Box::new(ref_expr),
                        new_val: Box::new(new_val),
                        range: Range::dummy(),
                    }
                } else {
                    ref_expr
                }
            });
        
        // Multiplicative operations
        let factor = assignment.clone()
            .then(just(Token::Times).ignore_then(assignment.clone()).repeated())
            .foldl(|lhs, rhs| Expr::Times(Box::new(lhs), Box::new(rhs), Range::dummy()));
        
        // Additive operations
        let term = factor.clone()
            .then(choice((
                just(Token::Plus).to(true),
                just(Token::Minus).to(false),
            )).then(factor.clone()).repeated())
            .foldl(|lhs, (is_plus, rhs)| {
                if is_plus {
                    Expr::Plus(Box::new(lhs), Box::new(rhs), Range::dummy())
                } else {
                    Expr::Minus(Box::new(lhs), Box::new(rhs), Range::dummy())
                }
            });
        
        // Comparison operations
        let comparison = term.clone()
            .then(choice((
                just(Token::Eq).to(0),
                just(Token::Leq).to(1),
                just(Token::Geq).to(2),
                just(Token::Lt).to(3),
                just(Token::Gt).to(4),
            )).then(term.clone()).or_not())
            .map(|(lhs, rhs_opt)| {
                if let Some((op_type, rhs)) = rhs_opt {
                    match op_type {
                        0 => Expr::Eq(Box::new(lhs), Box::new(rhs), Range::dummy()),
                        1 => Expr::Leq(Box::new(lhs), Box::new(rhs), Range::dummy()),
                        2 => Expr::Geq(Box::new(lhs), Box::new(rhs), Range::dummy()),
                        3 => Expr::Lt(Box::new(lhs), Box::new(rhs), Range::dummy()),
                        4 => Expr::Gt(Box::new(lhs), Box::new(rhs), Range::dummy()),
                        _ => unreachable!(),
                    }
                } else {
                    lhs
                }
            });
        
        // Sequence: expr ; expr
        let sequence = comparison.clone()
            .then(just(Token::Semicolon).ignore_then(comparison.clone()).repeated())
            .foldl(|first, second| Expr::Sequence {
                first: Box::new(first),
                second: Box::new(second),
                range: Range::dummy(),
            });
        
        sequence
    })
}

pub fn type_parser() -> impl Parser<Token, Ty, Error = Simple<Token>> + Clone {
    recursive(|ty| {
        let int_ty = just(Token::TypeInt).map(|_| Ty::IntTy(Range::dummy()));
        
        let id_ty = select! { Token::Id(name) => Ty::IdTy { name, range: Range::dummy() } };
        
        // Reference type: Ref type
        let ref_ty = just(Token::Ref)
            .ignore_then(ty.clone())
            .map(|contained_ty| Ty::RefTy {
                contained_ty: Box::new(contained_ty),
                range: Range::dummy(),
            });
        
        // Product type (tuples): (type, type, ...)
        let prod_ty = ty.clone()
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|components| {
                if components.len() == 1 {
                    components.into_iter().next().unwrap()
                } else {
                    Ty::ProdTy { components, range: Range::dummy() }
                }
            });
        
        let atom_ty = choice((int_ty, id_ty, ref_ty, prod_ty));
        
        // Function type: type -> type (right associative)
        let fun_ty = atom_ty.clone()
            .then(just(Token::To).ignore_then(ty.clone()).or_not())
            .map(|(dom, cod_opt)| {
                if let Some(cod) = cod_opt {
                    Ty::FunTy {
                        dom: Box::new(dom),
                        cod: Box::new(cod),
                        range: Range::dummy(),
                    }
                } else {
                    dom
                }
            });
        
        fun_ty
    })
}

pub fn typedef_parser() -> impl Parser<Token, Typedef, Error = Simple<Token>> {
    let variant = just(Token::Pipe)
        .ignore_then(select! { Token::Constructor(name) => name })
        .then_ignore(just(Token::Of))
        .then(type_parser())
        .map(|(constructor_name, ty)| Variant { constructor_name, ty });
    
    just(Token::Typedef)
        .ignore_then(select! { Token::Constructor(typename) => typename })
        .then_ignore(just(Token::Bind))
        .then(variant.repeated().at_least(1))
        .map(|(typename, variants)| Typedef {
            typename,
            variants,
            range: Range::dummy(),
        })
}

pub fn prog_parser() -> impl Parser<Token, Prog, Error = Simple<Token>> {
    typedef_parser()
        .repeated()
        .then(expr_parser())
        .map(|(typedefs, expr)| Prog { typedefs, expr })
        .then_ignore(end())
}

pub fn parse_expr(input: &str) -> Result<Expr, Vec<Simple<char>>> {
    let tokens = lexer().parse(input)?;
    expr_parser().parse(tokens).map_err(|errs| {
        errs.into_iter().map(|e| Simple::custom(e.span(), format!("{:?}", e))).collect()
    })
}

pub fn parse_prog(input: &str) -> Result<Prog, Vec<Simple<char>>> {
    let tokens = lexer().parse(input)?;
    prog_parser().parse(tokens).map_err(|errs| {
        errs.into_iter().map(|e| Simple::custom(e.span(), format!("{:?}", e))).collect()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_int() {
        let result = parse_expr("42");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Int(n, _) => assert_eq!(n, 42),
            _ => panic!("Expected Int expression"),
        }
    }

    #[test]
    fn test_parse_var() {
        let result = parse_expr("x");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Var(name, _) => assert_eq!(name, "x"),
            _ => panic!("Expected Var expression"),
        }
    }

    #[test]
    fn test_parse_addition() {
        let result = parse_expr("3 + 2");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Plus(_, _, _) => {},
            _ => panic!("Expected Plus expression"),
        }
    }

    #[test]
    fn test_parse_subtraction() {
        let result = parse_expr("5 - 3");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Minus(_, _, _) => {},
            _ => panic!("Expected Minus expression"),
        }
    }

    #[test]
    fn test_parse_multiplication() {
        let result = parse_expr("4 * 3");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Times(_, _, _) => {},
            _ => panic!("Expected Times expression"),
        }
    }

    #[test]
    fn test_parse_comparison() {
        let result = parse_expr("x == 5");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Eq(_, _, _) => {},
            _ => panic!("Expected Eq expression"),
        }
    }

    #[test]
    fn test_parse_let() {
        let result = parse_expr("let x = 42 in x + 1");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Let { bound_var, .. } => assert_eq!(bound_var, "x"),
            _ => panic!("Expected Let expression"),
        }
    }

    #[test]
    fn test_parse_let_rec() {
        let result = parse_expr("let rec f : int -> int = fun (x : int) -> x + 1 in f(5)");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::LetRec { bindings, .. } => assert_eq!(bindings.len(), 1),
            _ => panic!("Expected LetRec expression"),
        }
    }

    #[test]
    fn test_parse_fun_abstraction() {
        let result = parse_expr("fun (x : int) -> x + 1");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::FunAbstraction { formals, .. } => assert_eq!(formals.len(), 1),
            _ => panic!("Expected FunAbstraction expression"),
        }
    }

    #[test]
    fn test_parse_if_then_else() {
        let result = parse_expr("if x == 0 then 1 else 2");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::IfThenElse { .. } => {},
            _ => panic!("Expected IfThenElse expression"),
        }
    }

    #[test]
    fn test_parse_tuple() {
        let result = parse_expr("(1, 2, 3)");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Tuple(exprs, _) => assert_eq!(exprs.len(), 3),
            _ => panic!("Expected Tuple expression"),
        }
    }

    #[test]
    fn test_parse_empty_tuple() {
        let result = parse_expr("()");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Tuple(exprs, _) => assert_eq!(exprs.len(), 0),
            _ => panic!("Expected empty Tuple expression"),
        }
    }

    #[test] 
    fn test_parse_single_paren() {
        let result = parse_expr("(42)");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Int(n, _) => assert_eq!(n, 42),
            _ => panic!("Expected Int expression"),
        }
    }

    #[test]
    fn test_parse_let_tuple() {
        let result = parse_expr("let (x, y) = (1, 2) in x + y");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::LetTuple { component_vars, .. } => assert_eq!(component_vars.len(), 2),
            _ => panic!("Expected LetTuple expression"),
        }
    }

    #[test]
    fn test_parse_ref_constructor() {
        let result = parse_expr("ref 42");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::RefConstructor { .. } => {},
            _ => panic!("Expected RefConstructor expression"),
        }
    }

    #[test]
    fn test_parse_deref() {
        let result = parse_expr("!r");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Deref { .. } => {},
            _ => panic!("Expected Deref expression"),
        }
    }

    #[test]
    fn test_parse_assignment() {
        let result = parse_expr("r := 42");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Assign { .. } => {},
            _ => panic!("Expected Assign expression"),
        }
    }

    #[test]
    fn test_parse_sequence() {
        let result = parse_expr("x := 1; y := 2");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Sequence { .. } => {},
            _ => panic!("Expected Sequence expression"),
        }
    }

    #[test]
    fn test_parse_constructor_application() {
        let result = parse_expr("(Some 42)");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::ConstructorApplication { name, .. } => assert_eq!(name, "Some"),
            _ => panic!("Expected ConstructorApplication expression"),
        }
    }

    #[test]
    fn test_parse_match() {
        let result = parse_expr("match x with | Some y -> y");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Match { cases, .. } => assert_eq!(cases.len(), 1),
            _ => panic!("Expected Match expression"),
        }
    }

    #[test]
    fn test_parse_match_multiple_cases() {
        let result = parse_expr("match x with | Some y -> y | None z -> 0");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Match { cases, .. } => assert_eq!(cases.len(), 2),
            _ => panic!("Expected Match expression"),
        }
    }

    #[test]
    fn test_parse_match_with_guard() {
        let result = parse_expr("match x with | Some y when y > 0 -> y | _ -> 0");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Match { cases, .. } => {
                assert_eq!(cases.len(), 2);
                match &cases[0] {
                    MatchCase::ConstructorCase { when_cond, .. } => assert!(when_cond.is_some()),
                    _ => panic!("Expected ConstructorCase with guard"),
                }
            },
            _ => panic!("Expected Match expression"),
        }
    }

    #[test]
    fn test_parse_function_application() {
        let result = parse_expr("f(1, 2)");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Application { args, .. } => assert_eq!(args.len(), 2),
            _ => panic!("Expected Application expression"),
        }
    }

    #[test]
    fn test_parse_complex_expr() {
        let result = parse_expr("let f = fun (x : int) -> x * 2 in f(21)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_type_int() {
        let tokens = vec![Token::TypeInt];
        let result = type_parser().parse(tokens);
        assert!(result.is_ok());
        match result.unwrap() {
            Ty::IntTy(_) => {},
            _ => panic!("Expected IntTy"),
        }
    }

    #[test]
    fn test_parse_type_function() {
        let tokens = vec![Token::TypeInt, Token::To, Token::TypeInt];
        let result = type_parser().parse(tokens);
        assert!(result.is_ok());
        match result.unwrap() {
            Ty::FunTy { .. } => {},
            _ => panic!("Expected FunTy"),
        }
    }

    #[test]
    fn test_parse_type_product() {
        let tokens = vec![Token::LParen, Token::TypeInt, Token::Comma, Token::TypeInt, Token::RParen];
        let result = type_parser().parse(tokens);
        assert!(result.is_ok());
        match result.unwrap() {
            Ty::ProdTy { components, .. } => assert_eq!(components.len(), 2),
            _ => panic!("Expected ProdTy"),
        }
    }

    #[test]
    fn test_parse_typedef() {
        let input = "typedef Option = | Some of int | None of int";
        let tokens = lexer().parse(input).unwrap();
        let result = typedef_parser().parse(tokens);
        assert!(result.is_ok());
        match result.unwrap() {
            Typedef { typename, variants, .. } => {
                assert_eq!(typename, "Option");
                assert_eq!(variants.len(), 2);
            }
        }
    }

    #[test]
    fn test_parse_prog_with_typedef() {
        let input = "typedef Bool = | True of int | False of int\n42";
        let result = parse_prog(input);
        assert!(result.is_ok());
        match result.unwrap() {
            Prog { typedefs, expr } => {
                assert_eq!(typedefs.len(), 1);
                match expr {
                    Expr::Int(n, _) => assert_eq!(n, 42),
                    _ => panic!("Expected Int expression"),
                }
            }
        }
    }

    #[test]
    fn test_precedence() {
        let result = parse_expr("1 + 2 * 3");
        assert!(result.is_ok());
        match result.unwrap() {
            Expr::Plus(lhs, rhs, _) => {
                match (lhs.as_ref(), rhs.as_ref()) {
                    (Expr::Int(1, _), Expr::Times(_, _, _)) => {},
                    _ => panic!("Multiplication should have higher precedence"),
                }
            },
            _ => panic!("Expected Plus expression"),
        }
    }

    #[test]
    fn test_operator_precedence_complex() {
        let result = parse_expr("1 + 2 * 3 == 7");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_nested_let() {
        let result = parse_expr("let x = 1 in let y = 2 in x + y");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_factorial() {
        let input = "let rec fact : int -> int = fun (n : int) -> if n <= 1 then 1 else n * fact(n - 1) in fact(5)";
        let result = parse_expr(input);
        assert!(result.is_ok());
    }
}
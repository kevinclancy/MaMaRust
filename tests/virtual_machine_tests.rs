use mama_rust::syntax::{Ty, Expr};
use mama_rust::gen_code::{code_v, AddressGenerator, Context};
use mama_rust::exec::execute;
use mama_rust::virtual_machine::{from_instructions};
use mama_rust::test_utils::{parse_expr, parse_prog};
use mama_rust::{address_resolution, code_builder};

fn run_test_expr(expr_str: &str, expected_result: i32) {
    let e = parse_expr(expr_str).unwrap();
    let mut context = Context::new();
    let mut addr_generator = AddressGenerator::new();

    let (ty, code) = code_v(&mut context, &mut addr_generator, &e, 0i16).unwrap();

    match ty {
        Ty::IntTy(_) => {},
        _ => panic!("Expected type to be int, got: {:?}", ty),
    }

    let mut code_vec : Vec<i32> = code.into_iter().collect();
    code_vec.push(code_builder::halt());

    let resolved_code_vec = address_resolution::resolve(&code_vec);

    let mut vm = from_instructions(resolved_code_vec);
    let result = execute(&mut vm);

    assert_eq!(result, expected_result);
}

#[test]
fn sum_two_ints() {
    run_test_expr("3 + 2", 5);
}

#[test]
fn test_apply() {
    run_test_expr("(fun (x : int) (y : int) -> x + y) 3 2", 5);
}

#[test]
fn test_let_apply() {
    run_test_expr("let f = fun (x : int) -> x + 1 in f 5", 6);
}

#[test]
fn test_let() {
    run_test_expr("let x = 3 in x + 2", 5);
}

#[test]
fn test_fun() {
    run_test_expr("let f = fun (x : int) -> x + 1 in 2", 2);
}


#[test]
fn test_call_and_use() {
    run_test_expr("let f = fun (x : int) -> x + 1 in (f 5) + 2", 8);
}

#[test]
fn test_if_then_else() {
    run_test_expr("if 3 <= 5 then 1 else 0", 1);
}

#[test]
fn test_multiplication() {
    run_test_expr("3 * 4", 12);
}

#[test]
fn test_subtraction() {
    run_test_expr("10 - 3", 7);
}

#[test]
fn test_comparison_leq() {
    run_test_expr("3 <= 5", 1);
}

#[test]
fn test_comparison_gt() {
    run_test_expr("5 > 3", 1);
}

#[test]
fn test_nested_arithmetic() {
    run_test_expr("(2 + 3) * (4 - 1)", 15);
}

#[test]
#[ignore = "Requires tuple implementation"]
fn test_tuple() {
    run_test_expr("let (x, y) = (3, 4) in x + y", 7);
}

#[test]
#[ignore = "Requires reference implementation"]
fn test_ref() {
    run_test_expr("let r = ref 5 in !r", 5);
}

#[test]
#[ignore = "Requires reference assignment implementation"]
fn test_assign() {
    run_test_expr("let r = ref 5 in r := 10; !r", 10);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match() {
    panic!("Pattern matching tests require type definitions");
}

#[test]
#[ignore = "Requires recursive function implementation"]
fn test_factorial() {
    run_test_expr("let rec fact = fun (n : int) -> if n <= 1 then 1 else n * (fact (n - 1)) in fact 5", 120);
}
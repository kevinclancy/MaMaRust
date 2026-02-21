use mama_rust::syntax::{Ty, Expr};
use mama_rust::gen_code::{code_v, gen_code_prog, AddressGenerator, Context};
use mama_rust::exec::execute;
use mama_rust::virtual_machine::{from_instructions};
use mama_rust::test_utils::{parse_expr, parse_prog};
use mama_rust::{address_resolution, code_builder};

// fn run_test_expr(expr_str: &str, expected_result: i32) {
//     let e = parse_expr(expr_str).unwrap();
//     let mut context = Context::new();
//     let mut addr_generator = AddressGenerator::new();

//     let (ty, code) = code_v(&mut context, &mut addr_generator, &e, 0u8).unwrap();

//     match ty {
//         Ty::IntTy(_) => {},
//         _ => panic!("Expected type to be int, got: {:?}", ty),
//     }

//     let mut code_vec : Vec<i32> = code.into_iter().collect();
//     code_vec.push(code_builder::halt());

//     let resolved_code_vec = address_resolution::resolve(&code_vec);

//     let mut vm = from_instructions(resolved_code_vec);
//     let result = execute(&mut vm);

//     assert_eq!(result, expected_result);
// }

fn run_test_prog(prog_str: &str, expected_result: i32) {
    let prog = parse_prog(prog_str).unwrap();
    let (ty, code) = gen_code_prog(&prog).unwrap();

    let mut code_vec : Vec<i32> = code.into_iter().collect();
    code_vec.push(code_builder::halt());

    let resolved_code_vec = address_resolution::resolve(&code_vec);

    let mut vm = from_instructions(resolved_code_vec);
    let result = execute(&mut vm);

    assert_eq!(result, expected_result);
}

#[test]
fn sum_two_ints() {
    run_test_prog("3 + 2", 5);
}

#[test]
fn test_apply() {
    run_test_prog("(fun (x : int, y : int) -> x + y) 3 2", 5);
}

#[test]
fn test_let_apply() {
    run_test_prog("let f = fun (x : int) -> x + 1 in f 5", 6);
}

#[test]
fn test_let() {
    run_test_prog("let x = 3 in x + 2", 5);
}

#[test]
fn test_fun() {
    run_test_prog("let f = fun (x : int) -> x + 1 in 2", 2);
}


#[test]
fn test_call_and_use() {
    run_test_prog("let f = fun (x : int) -> x + 1 in (f 5) + 2", 8);
}

#[test]
fn test_if_then_else() {
    run_test_prog("if 3 <= 5 then 1 else 0", 1);
}

#[test]
fn test_multiplication() {
    run_test_prog("3 * 4", 12);
}

#[test]
fn test_subtraction() {
    run_test_prog("10 - 3", 7);
}

#[test]
fn test_comparison_leq() {
    run_test_prog("3 <= 5", 1);
}

#[test]
fn test_comparison_gt() {
    run_test_prog("5 > 3", 1);
}

#[test]
fn test_nested_arithmetic() {
    run_test_prog("(2 + 3) * (4 - 1)", 15);
}

#[test]
fn test_multi_call() {
    run_test_prog("let a = fun (x : int, y : int) -> x + y in a (3 + 2) 1", 6);
}

#[test]
fn test_two_calls() {
    run_test_prog("let a = fun (x : int, y : int) -> x + y in (a 3 2) + (a 1 4)", 10);
}

#[test]
fn test_under_supply() {
    run_test_prog("let a = fun (x : int, y : int) -> x + y in let b = a 3 in b 2", 5);
}

#[test]
fn test_over_supply() {
    run_test_prog("let a = fun (x : int) -> fun (y : int) -> x + y in a 3 2", 5);
}

#[test]
fn test_call_arg() {
    run_test_prog("let a = fun (x : int, y : int) -> x + y in a (a 3 2) 1", 6);
}

#[test]
fn test_call_arg2() {
    run_test_prog("let a = fun (x : int, y : int) -> x + y in a 1 (a 3 2)", 6);
}

#[test]
fn test_tuple() {
    run_test_prog("let (x, y) = (3, 4) in x + y", 7);
}

#[test]
fn test_ref() {
    run_test_prog("let r = ref 5 in !r", 5);
}

#[test]
fn test_assign() {
    run_test_prog("let r = ref 5 in r := 10; !r", 10);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match() {
    run_test_prog("match Some 5 with | Some x -> x | None -> 0", 5);
}

#[test]
fn test_factorial() {
    run_test_prog("let rec fact : int -> int = fun (n : int) -> if n <= 1 then 1 else n * (fact (n - 1)) in fact 4", 24);
}

#[test]
fn test_empty_tuple() {
    run_test_prog("let () = () in 1", 1);
}

#[test]
fn test_fact_tuple() {
    run_test_prog("let rec fact : int -> int = fun (n : int) -> if n <= 1 then 1 else n * (fact (n - 1)) in let (x, y) = (fact 3, fact 4) in x + y", 30);
}

#[test]
fn test_assign_add() {
    run_test_prog("let a = ref 0 in a := !a + 2; !a", 2);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match2() {
    run_test_prog("match Some 42 with | Some x -> x | None -> 0", 42);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match3() {
    run_test_prog("match (1, 2) with | (x, y) -> x + y", 3);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match_guard_false() {
    run_test_prog("match 5 with | x when x > 10 -> 1 | _ -> 0", 0);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match_guard_true() {
    run_test_prog("match 15 with | x when x > 10 -> 1 | _ -> 0", 1);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match_fall_through() {
    run_test_prog("match 2 with | 1 -> 10 | 2 -> 20 | _ -> 30", 20);
}

#[test]
#[ignore = "Requires pattern matching implementation"]
fn test_match_catch_all_guard() {
    run_test_prog("match 5 with | x when x > 10 -> 1 | _ -> 0", 0);
}

#[test]
fn cbv_application() {
    run_test_prog("let z = ref 0 in let a = fun (x : int, y : int) -> !z + x + y in z := !z + 1; a (z := !z + 1; 1) (z := !z + 1; 1)", 5);
}

#[test]
fn cbv_constructor() {
    run_test_prog(
        "typedef Option = | Some {val : int} | None {} \
         let z = ref 0 in z := !z + 1; let q = (Some { val : !z }) in 1",
    1);
}

#[test]
fn cbv_tuples() {
    run_test_prog("let z = ref 0 in z := !z + 1; let (a,b) = (!z, !z) in a", 1);
}

#[test]
fn cbv_let() {
    run_test_prog("let z = ref 3 in let x = (z := !z + 1; !z) in x", 4);
}

#[test]
fn tail_lite() {
    run_test_prog("let rec foo : int -> int = fun (z : int) -> if z == 5 then 1 else foo (z + 1) in foo 0", 1);
}

#[test]
fn tail_call() {
    run_test_prog("let rec foo : int -> int = fun (z : int) -> if z == 300000 then 1 else foo (z + 1) in foo 0", 1);
}

#[test]
fn test_dont_collect_gp() {
    run_test_prog(
        "let mkIncrementer = fun () -> \
            let rec foo : int -> int = fun (z : int) -> \
                if z == 100000 then 1 else foo (z + 1) \
            in fun () -> foo 0 \
         in (mkIncrementer ()) ()",
        1
    );
}

#[test]
fn test_dont_collect_gp2() {
    run_test_prog(
        "let mkFoo = fun () -> \
            let z = ref 0 in \
            let rec foo : int -> int = fun (x : int) -> \
                if x == 100000 then (z := !z + 1; !z) else foo (x + 1) \
            in foo \
         in (mkFoo ()) 0",
        1
    );
}
use mama_rust::syntax::{Expr, Prog, Ty};
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

/// Wraps a test program's trailing expression in the `run` component that a program must
/// define, leaving any leading `typedef` declarations as sibling components. The split
/// point is found by trying every position at which the remainder parses as an expression
fn as_module_prog(prog_str: &str) -> String {
    for split in prog_str.char_indices().map(|(i, _)| i).chain([prog_str.len()]) {
        let (typedefs, body) = prog_str.split_at(split);
        if body.trim().is_empty() {
            continue;
        }
        let candidate = format!("{} val run = fun () -> ({})", typedefs, body);
        if parse_prog(&candidate).is_ok() {
            return candidate;
        }
    }
    panic!("could not find a split point that parses: {}", prog_str)
}

/// Parses and runs a program already in module form (its own `val run = ...`)
fn run_module_prog(prog_str: &str, expected_result: i32) {
    let prog = parse_prog(prog_str).unwrap();
    let prog2 = Prog::stamp_ids(&prog).unwrap();
    let (_ty, code) = gen_code_prog(&prog2).unwrap();

    let mut code_vec : Vec<i32> = code.into_iter().collect();
    code_vec.push(code_builder::halt());

    let resolved_code_vec = address_resolution::resolve(&code_vec);

    let mut vm = from_instructions(resolved_code_vec);
    let result = execute(&mut vm);

    assert_eq!(result, expected_result);
}

/// Asserts that a program in module form fails code generation with a message containing
/// `expected_msg`
fn assert_prog_type_error(prog_str: &str, expected_msg: &str) {
    let prog = parse_prog(prog_str).unwrap();
    let prog2 = Prog::stamp_ids(&prog).unwrap();
    match gen_code_prog(&prog2) {
        Ok(_) => panic!("expected a type error, but the program compiled"),
        Err((msg, _)) => assert!(msg.contains(expected_msg)),
    }
}

fn run_test_prog(prog_str: &str, expected_result: i32) {
    let prog = parse_prog(&as_module_prog(prog_str)).unwrap();
    let prog2 = Prog::stamp_ids(&prog).unwrap();
    let (ty, code) = gen_code_prog(&prog2).unwrap();

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
fn test_match() {
    run_test_prog(
        "typedef Option = | Some {contents : int} | None {} \
         match Some {contents : 5} with | Some {contents : x} -> x | None {} -> 0",
        5
    );
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
fn test_match2() {
    run_test_prog(
        "typedef Option = | Some {contents : int} | None {} \
         match Some {contents : 42} with | Some {contents : x} -> x | None {} -> 0",
        42
    );
}

#[test]
fn test_match3() {
    run_test_prog("match (1, 2) with | (x, y) -> x + y", 3);
}

#[test]
fn test_match_guard_false() {
    run_test_prog("match 5 with | x when x > 10 -> 1 | _ -> 0", 0);
}

#[test]
fn test_match_guard_true() {
    run_test_prog("match 15 with | x when x > 10 -> 1 | _ -> 0", 1);
}

#[test]
fn test_match_fall_through() {
    run_test_prog("match 2 with | 1 -> 10 | 2 -> 20 | _ -> 30", 20);
}

#[test]
fn test_match_catch_all_guard() {
    run_test_prog("match 5 with | x when x > 10 -> 1 | _ -> 0", 0);
}

#[test]
fn test_let_constructor_pattern() {
    run_test_prog(
        "typedef Option = | Some {contents : int} | None {} \
         let Some {contents : x} = Some {contents : 42} in x",
        42
    );
}

#[test]
fn test_let_constructor_pattern_add_fields() {
    run_test_prog(
        "typedef Pair = | MkPair {fst : int, snd : int} \
         let MkPair {fst : a, snd : b} = MkPair {fst : 3, snd : 4} in a + b",
        7
    );
}

#[test]
fn test_let_constructor_pattern_tuple_fields() {
    run_test_prog(
        "typedef Pair = | MkPair {fst : (int, int, int), snd : (int, int, int)} \
         let MkPair {fst : (a, b, c), snd : (d, e, f)} = MkPair {fst : (1, 2, 3), snd : (4, 5, 6)} in a + b + c + d + e + f",
        21
    );
}

#[test]
fn test_let_constructor_nested_tuple() {
    run_test_prog(
        "typedef Wrapper = | Wrap {contents : (int, int)} \
         let Wrap {contents : (x, y)} = Wrap {contents : (10, 20)} in x + y",
        30
    );
}

#[test]
fn cbv_application() {
    run_test_prog("let z = ref 0 in let a = fun (x : int, y : int) -> !z + x + y in z := !z + 1; a (z := !z + 1; 1) (z := !z + 1; 1)", 5);
}

#[test]
fn cbv_constructor() {
    run_test_prog(
        "typedef Option = | Some {contents : int} | None {} \
         let z = ref 0 in z := !z + 1; let q = (Some { contents : !z }) in 1",
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
#[test]
fn module_val_projection() {
    run_module_prog(
        "module M = mod val x = 42 end \
         val run = fun () -> M.x",
        42
    );
}

#[test]
fn module_fun_projection() {
    run_module_prog(
        "module M = mod val double = fun (a : int) -> a * 2 end \
         val run = fun () -> M.double 21",
        42
    );
}

#[test]
fn module_telescoping_fields() {
    run_module_prog(
        "module M = mod val x = 10 val y = x + 5 end \
         val run = fun () -> M.y",
        15
    );
}

#[test]
fn module_backward_reference() {
    run_module_prog(
        "module M = mod val x = 5 end \
         module N = mod val y = M.x + 1 end \
         val run = fun () -> N.y + M.x",
        11
    );
}

#[test]
fn nested_module_projection() {
    run_module_prog(
        "module A = mod \
            module B = mod val y = 7 end \
            val x = B.y + 3 \
         end \
         val run = fun () -> A.B.y + A.x",
        17
    );
}

#[test]
fn module_interleaved_type_fields() {
    run_module_prog(
        "module M = mod \
            type t = int \
            val a = 10 \
            typedef Opt = | None {} \
            val b = 20 \
         end \
         val run = fun () -> M.a + M.b",
        30
    );
}

#[test]
fn module_sum_type_values() {
    run_module_prog(
        "module M = mod \
            typedef Opt = | Some {contents : int} | None {} \
            val mk = fun (n : int) -> Some {contents : n} \
            val get = fun (o : Opt) -> match o with | Some {contents : x} -> x | None {} -> 0 \
         end \
         val run = fun () -> M.get (M.mk 5)",
        5
    );
}

#[test]
fn nested_module_sum_type() {
    run_module_prog(
        "module A = mod \
            module B = mod \
                typedef Opt = | Some {contents : int} | None {} \
                val mk = fun (n : int) -> Some {contents : n} \
                val get = fun (o : Opt) -> match o with | Some {contents : x} -> x | None {} -> 0 \
            end \
            val y = B.get (B.mk 7) \
         end \
         val run = fun () -> A.y",
        7
    );
}

// Two modules each define a type named `T`. Stamping gives the two `T`s distinct
// identifiers, so values of one never satisfy a function expecting the other.
const TWO_MODULES_NAMED_T: &str =
    "module M = mod \
        typedef T = | A {v : int} \
        val mk = fun (n : int) -> A {v : n} \
        val get = fun (t : T) -> match t with | A {v : x} -> x \
     end \
     module N = mod \
        typedef T = | B {v : int} \
        val mk = fun (n : int) -> B {v : n} \
        val get = fun (t : T) -> match t with | B {v : x} -> x \
     end ";

#[test]
fn stamping_keeps_same_named_types_usable() {
    run_module_prog(
        &format!("{} val run = fun () -> M.get (M.mk 1) + N.get (N.mk 2)", TWO_MODULES_NAMED_T),
        3
    );
}

#[test]
fn stamping_rejects_crossed_same_named_types() {
    assert_prog_type_error(
        &format!("{} val run = fun () -> M.get (N.mk 2)", TWO_MODULES_NAMED_T),
        "argument type mismatch"
    );
}

#[test]
fn stamping_keeps_shadowed_type_live() {
    run_module_prog(
        "module M = mod \
            typedef T = | A {v : int} \
            val fromOld = fun (t : T) -> match t with | A {v : x} -> x \
            val oldVal = fromOld (A {v : 41}) \
            typedef T = | B {v : int} \
            val mkNew = fun (n : int) -> B {v : n} \
            val newVal = match mkNew 1 with | B {v : x} -> x \
         end \
         val run = fun () -> M.oldVal + M.newVal",
        42
    );
}

#[test]
fn stamping_rejects_shadowed_type_confusion() {
    assert_prog_type_error(
        "module M = mod \
            typedef T = | A {v : int} \
            val fromOld = fun (t : T) -> match t with | A {v : x} -> x \
            typedef T = | B {v : int} \
            val mkNew = fun (n : int) -> B {v : n} \
            val bad = fromOld (mkNew 1) \
         end \
         val run = fun () -> M.bad",
        "argument type mismatch"
    );
}

#[test]
fn shadowed_val_resolves_to_last() {
    run_module_prog(
        "module M = mod val x = 1 val x = 2 end \
         val run = fun () -> M.x",
        2
    );
}

// A reference inside the module sees the binding in scope where it appears, while a
// projection from outside sees the last one, so both agree on which `x` they name.
#[test]
fn shadowed_val_agrees_inside_and_outside() {
    run_module_prog(
        "module M = mod \
            val x = 1 \
            val fromFirst = x \
            val x = 20 \
            val fromSecond = x \
         end \
         val run = fun () -> M.fromFirst + M.fromSecond + M.x",
        41
    );
}

// The later `T` shadows the earlier one, so a projected function annotated with `T`
// takes values of the later type.
#[test]
fn shadowed_type_resolves_to_last() {
    run_module_prog(
        "module M = mod \
            typedef T = | A {v : int} \
            typedef T = | B {v : int} \
            val mk = fun (n : int) -> B {v : n} \
            val get = fun (t : T) -> match t with | B {v : x} -> x \
         end \
         val run = fun () -> M.get (M.mk 7)",
        7
    );
}

#[test]
fn nested_module_referenced_from_closure() {
    run_module_prog(
        "module A = mod \
            module B = mod val y = 7 end \
            val f = fun (n : int) -> B.y + n \
         end \
         val run = fun () -> A.f 3",
        10
    );
}

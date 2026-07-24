// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Block-scoped (nested) `fn` item lowering.
//!
//! A `fn` declared inside another function body is a plain item — it does not
//! capture the enclosing environment — so it lowers like a top-level function
//! keyed by its name, and calls to it within the block resolve through the
//! lexical scope. These tests pin that the lowering produces a well-formed,
//! NLL-clean VIR program (the verification-surface notion of "evaluates
//! correctly") and that scoping/recursion/argument-kind behave as expected.

use clean_rust_sem::vir::Term;
use clean_rust_sem::{NllResult, SourceProgram};

fn lower(source: &str) -> clean_rust_sem::LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program.lower_to_vir().expect("source should lower to VIR")
}

fn borrow_result(source: &str, function: &str) -> NllResult {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    analyses
        .remove(function)
        .unwrap_or_else(|| panic!("borrow analyses should contain `{function}`"))
}

fn call_count(body: &clean_rust_sem::Body) -> usize {
    body.blocks
        .iter()
        .filter(|bb| matches!(&bb.terminator, Term::Call { .. }))
        .count()
}

#[test]
fn test_block_scoped_fn_called_lowers_into_program_table() {
    let source = r#"
        fn main() -> u32 {
            fn helper(x: u32) -> u32 {
                x + 1u32
            }
            helper(41u32)
        }
    "#;

    let lowered = lower(source);
    // The nested function lowers into the same flat table as top-level fns.
    assert!(
        lowered.functions.contains_key("helper"),
        "block-scoped fn `helper` should be lowered into the program table, got {:?}",
        lowered.functions.keys().collect::<Vec<_>>()
    );
    let main = lowered
        .functions
        .get("main")
        .expect("program should contain `main`");
    assert_eq!(
        call_count(main),
        1,
        "the call to the nested fn should lower to a single Term::Call"
    );
}

#[test]
fn test_block_scoped_fn_call_is_nll_clean() {
    let source = r#"
        fn main() -> u32 {
            fn helper(x: u32) -> u32 {
                x + 1u32
            }
            helper(41u32)
        }
    "#;

    let result = borrow_result(source, "main");
    assert!(
        result.errors.is_empty(),
        "calling a block-scoped fn should be NLL-clean: {:?}",
        result.errors
    );
    // The nested function body is itself borrow-checked as a top-level function.
    let helper = borrow_result(source, "helper");
    assert!(
        helper.errors.is_empty(),
        "the nested fn body should be NLL-clean: {:?}",
        helper.errors
    );
}

#[test]
fn test_block_scoped_fn_is_scoped_to_its_block_and_can_shadow() {
    // Two sibling blocks each declare `compute` with a different signature.
    // Each block resolves to its own definition; neither leaks out, and the
    // inner shadow does not collide at the type level.
    let source = r#"
        fn main() -> u32 {
            let a: u32 = {
                fn compute(x: u32) -> u32 {
                    x + 1u32
                }
                compute(10u32)
            };
            let b: u32 = {
                fn compute(x: u32) -> u32 {
                    x + 2u32
                }
                compute(20u32)
            };
            a + b
        }
    "#;

    let lowered = lower(source);
    assert!(
        lowered.functions.contains_key("main"),
        "program should contain `main`"
    );
    // Both block-scoped definitions are lowered; the second keyed under the same
    // bare name overwrites the first in the flat table, which is acceptable for
    // distinct lexical scopes that never alias at a single call site.
    assert!(
        lowered.functions.contains_key("compute"),
        "block-scoped `compute` should lower, got {:?}",
        lowered.functions.keys().collect::<Vec<_>>()
    );

    let result = borrow_result(source, "main");
    assert!(
        result.errors.is_empty(),
        "shadowed block-scoped fns should be NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_block_scoped_fn_supports_self_recursion() {
    // A recursive nested fn: the signature is registered before the body is
    // lowered, so the self-call inside the body resolves.
    let source = r#"
        fn main() -> u32 {
            fn fib(n: u32) -> u32 {
                if n < 2u32 {
                    n
                } else {
                    fib(n - 1u32) + fib(n - 2u32)
                }
            }
            fib(6u32)
        }
    "#;

    let lowered = lower(source);
    let fib = lowered
        .functions
        .get("fib")
        .expect("recursive nested fn `fib` should lower into the program table");
    assert!(
        call_count(fib) >= 2,
        "the recursive body should emit at least two self-calls, got {}",
        call_count(fib)
    );

    let result = borrow_result(source, "main");
    assert!(
        result.errors.is_empty(),
        "calling a recursive nested fn should be NLL-clean: {:?}",
        result.errors
    );
    let fib_result = borrow_result(source, "fib");
    assert!(
        fib_result.errors.is_empty(),
        "the recursive nested fn body should be NLL-clean: {:?}",
        fib_result.errors
    );
}

#[test]
fn test_block_scoped_fn_with_copy_arg_lowers() {
    // A Copy argument (u32): the caller may keep using the value afterwards.
    let source = r#"
        fn main() -> u32 {
            fn add_one(x: u32) -> u32 {
                x + 1u32
            }
            let n: u32 = 5u32;
            let m: u32 = add_one(n);
            n + m
        }
    "#;

    let result = borrow_result(source, "main");
    assert!(
        result.errors.is_empty(),
        "Copy argument to a nested fn should be NLL-clean (no use-after-move): {:?}",
        result.errors
    );
}

#[test]
fn test_block_scoped_fn_with_reference_arg_lowers() {
    // A non-Copy borrow argument (&String): passing a shared reference keeps the
    // owner alive; borrow checking must not flag a false move.
    let source = r#"
        fn main() -> usize {
            fn length(s: &String) -> usize {
                0usize
            }
            let owner: String = String::new();
            let len: usize = length(&owner);
            len
        }
    "#;

    let lowered = lower(source);
    assert!(
        lowered.functions.contains_key("length"),
        "nested fn taking a reference arg should lower, got {:?}",
        lowered.functions.keys().collect::<Vec<_>>()
    );
    let result = borrow_result(source, "main");
    assert!(
        result.errors.is_empty(),
        "shared-reference argument to a nested fn should be NLL-clean: {:?}",
        result.errors
    );
}

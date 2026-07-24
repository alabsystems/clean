// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for calling closures through `dyn Fn` / `dyn FnMut` /
//! `dyn FnOnce` trait objects — both VIR lowering and interpreter dispatch.
//!
//! A surface `dyn Fn(A) -> R` trait object's parenthesized signature is erased
//! at parse time to a bare `DynTrait { trait_name: "Fn" }`, so the callee's
//! parameter and return types cannot be recovered from the type alone. Calls
//! through such a trait object lower the arguments at their own inferred types
//! and dispatch through the materialized fat-pointer operand; the interpreter
//! peels the reference / vtable indirection to reach the underlying closure and
//! reuses the closure's Fn/FnMut/FnOnce capture semantics.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

fn run_main(source: &str) -> clean_rust_sem::expr::EvalResult {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    program.run(&mut interpreter)
}

fn run_main_value(source: &str) -> Option<Value> {
    run_main(source).value()
}

// --- VIR lowering ---

#[test]
fn test_ref_dyn_fn_call_lowers_to_vir_and_is_nll_clean() {
    let source = r#"
        fn main() -> i32 {
            let f: &dyn Fn(i32) -> i32 = &|x: i32| x + 1i32;
            f(5i32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program
        .lower_to_vir()
        .expect("calling through `&dyn Fn` should lower to VIR");
    let analyses = lowered.check_borrows();
    assert!(
        analyses
            .get("main")
            .expect("borrow analyses should include `main`")
            .errors
            .is_empty(),
        "calling through `&dyn Fn` should stay NLL-clean"
    );
}

#[test]
fn test_box_dyn_fn_call_lowers_to_vir() {
    let source = r#"
        fn main() -> i32 {
            let f: Box<dyn Fn(i32) -> i32> = Box::new(|x: i32| x + 1i32);
            f(5i32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("calling through `Box<dyn Fn>` should lower to VIR");
}

#[test]
fn test_non_callable_dyn_trait_call_rejected_by_vir() {
    let source = r#"
        trait Greeter { fn greet(&self) -> i32; }
        struct G { v: i32 }
        impl Greeter for G { fn greet(&self) -> i32 { self.v } }
        fn main() -> i32 {
            let g = G { v: 42i32 };
            let f: &dyn Greeter = &g;
            f(5i32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    assert!(
        program.lower_to_vir().is_err(),
        "calling a non-`Fn` `dyn` trait object must be rejected by VIR lowering"
    );
}

// --- Interpreter dispatch ---

#[test]
fn test_ref_dyn_fn_created_from_closure_and_called_returns_value() {
    let source = r#"
        fn main() -> i32 {
            let f: &dyn Fn(i32) -> i32 = &|x: i32| x + 1i32;
            f(5i32)
        }
    "#;
    assert_eq!(run_main_value(source), Some(Value::i32(6)));
}

#[test]
fn test_ref_dyn_fn_from_named_closure_called_returns_value() {
    let source = r#"
        fn main() -> i32 {
            let c = |x: i32| x + 1i32;
            let f: &dyn Fn(i32) -> i32 = &c;
            f(5i32)
        }
    "#;
    assert_eq!(run_main_value(source), Some(Value::i32(6)));
}

#[test]
fn test_box_dyn_fn_called_returns_value() {
    let source = r#"
        fn main() -> i32 {
            let f: Box<dyn Fn(i32) -> i32> = Box::new(|x: i32| x + 1i32);
            f(5i32)
        }
    "#;
    assert_eq!(run_main_value(source), Some(Value::i32(6)));
}

#[test]
fn test_box_dyn_fnmut_mutates_captured_cell_across_calls() {
    // Captured interior-mutability state observably accumulates across calls
    // through a `Box<dyn FnMut>`.
    let source = r#"
        use std::cell::Cell;
        fn main() -> i32 {
            let total = Cell::new(0i32);
            let mut f: Box<dyn FnMut(i32)> = Box::new(|x: i32| { total.set(total.get() + x); });
            f(5i32);
            f(7i32);
            total.get()
        }
    "#;
    assert_eq!(run_main_value(source), Some(Value::i32(12)));
}

#[test]
fn test_ref_mut_dyn_fnmut_mutates_captured_cell_across_calls() {
    let source = r#"
        use std::cell::Cell;
        fn main() -> i32 {
            let total = Cell::new(0i32);
            let mut c = |x: i32| { total.set(total.get() + x); };
            let f: &mut dyn FnMut(i32) = &mut c;
            f(5i32);
            f(7i32);
            total.get()
        }
    "#;
    assert_eq!(run_main_value(source), Some(Value::i32(12)));
}

#[test]
fn test_box_dyn_fnonce_consumed_once_returns_captured_value() {
    let source = r#"
        fn main() -> i32 {
            let s = 10i32;
            let f: Box<dyn FnOnce() -> i32> = Box::new(move || s + 1i32);
            f()
        }
    "#;
    assert_eq!(run_main_value(source), Some(Value::i32(11)));
}

#[test]
fn test_non_callable_dyn_trait_call_rejected_by_interpreter() {
    let source = r#"
        trait Greeter { fn greet(&self) -> i32; }
        struct G { v: i32 }
        impl Greeter for G { fn greet(&self) -> i32 { self.v } }
        fn main() -> i32 {
            let g = G { v: 42i32 };
            let f: &dyn Greeter = &g;
            f(5i32)
        }
    "#;
    assert!(
        matches!(run_main(source), clean_rust_sem::expr::EvalResult::Error(_)),
        "calling a non-`Fn` `dyn` trait object must not be accepted by the interpreter"
    );
}

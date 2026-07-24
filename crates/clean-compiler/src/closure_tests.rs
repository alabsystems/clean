// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for closure creation and capture.
//!
//! Part of #3084 - Runtime closure support.

use super::*;
use crate::lcnf::{Arg, Code, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};
use std::collections::{HashMap, HashSet};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Helper: set of FVarIds from a slice of u64s.
fn bound_set(ids: &[u64]) -> HashSet<FVarId> {
    ids.iter().map(|n| fvar(*n)).collect()
}

// ────────────────────────────────────────────────────────────────────────
// CaptureMode tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_capture_mode_equality() {
    assert_eq!(CaptureMode::ByValue, CaptureMode::ByValue);
    assert_eq!(CaptureMode::ByRef, CaptureMode::ByRef);
    assert_ne!(CaptureMode::ByValue, CaptureMode::ByRef);
}

// ────────────────────────────────────────────────────────────────────────
// ClosureBuilder basic tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_builder_empty_captures() {
    let builder = ClosureBuilder::new(fvar(100), 2);
    let env = builder.build();

    assert_eq!(env.capture_count(), 0);
    assert_eq!(env.param_count, 2);
    assert_eq!(env.body_fvar, fvar(100));
    assert!(env.all_by_value()); // vacuously true
}

#[test]
fn test_builder_add_captures() {
    let mut builder = ClosureBuilder::new(fvar(100), 1);
    builder.add_capture(fvar(10), name("x"), 0, CaptureMode::ByValue);
    builder.add_capture(fvar(20), name("y"), 1, CaptureMode::ByRef);
    let env = builder.build();

    assert_eq!(env.capture_count(), 2);
    assert!(!env.all_by_value());

    let cap_x = env.find_capture(fvar(10)).expect("should find x");
    assert_eq!(cap_x.index, 0);
    assert_eq!(cap_x.capture_mode, CaptureMode::ByValue);

    let cap_y = env.find_capture(fvar(20)).expect("should find y");
    assert_eq!(cap_y.index, 1);
    assert_eq!(cap_y.capture_mode, CaptureMode::ByRef);
}

#[test]
fn test_builder_find_capture_missing() {
    let builder = ClosureBuilder::new(fvar(100), 1);
    let env = builder.build();
    assert!(env.find_capture(fvar(999)).is_none());
}

// ────────────────────────────────────────────────────────────────────────
// ClosureBuilder::from_fun_decl tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_from_fun_decl_no_free_vars() {
    // fun f (x : Nat) := return x
    // No free variables — all references are to the parameter.
    let fun_decl = FunDecl::new(
        fvar(100),
        name("f"),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(1)),
    );
    let bound = bound_set(&[]);
    let builder = ClosureBuilder::from_fun_decl(&fun_decl, &bound);
    let env = builder.build();

    assert_eq!(env.capture_count(), 0, "no free vars means no captures");
    assert_eq!(env.param_count, 1);
}

#[test]
fn test_from_fun_decl_captures_free_var() {
    // outer: let z = ...
    // fun f (x : Nat) := let r = z + x; return r
    // z is free in f's body (not a param, not bound inside f)
    let fun_decl = FunDecl::new(
        fvar(100),
        name("f"),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        nat_type(),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("r"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(50)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    // fvar(50) = z is in the enclosing scope
    let bound = bound_set(&[50]);
    let builder = ClosureBuilder::from_fun_decl(&fun_decl, &bound);
    let env = builder.build();

    assert_eq!(env.capture_count(), 1, "z should be captured");
    let cap = env.find_capture(fvar(50)).expect("should capture z");
    assert_eq!(cap.capture_mode, CaptureMode::ByValue);
}

#[test]
fn test_from_fun_decl_multiple_captures() {
    // fun f (x) := let r = a + b + x; return r
    // a (fvar 10) and b (fvar 20) are free
    let fun_decl = FunDecl::new(
        fvar(100),
        name("f"),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        nat_type(),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("ab"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("r"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(1))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let bound = bound_set(&[10, 20]);
    let builder = ClosureBuilder::from_fun_decl(&fun_decl, &bound);
    let env = builder.build();

    assert_eq!(env.capture_count(), 2, "a and b should be captured");
    assert!(env.find_capture(fvar(10)).is_some());
    assert!(env.find_capture(fvar(20)).is_some());
    assert!(env.all_by_value());
}

// ────────────────────────────────────────────────────────────────────────
// free_variables wrapper tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_free_variables_simple() {
    let code = Code::ret(fvar(5));
    let bound = bound_set(&[]);
    let free = free_variables(&code, &bound);
    assert!(free.contains(&fvar(5)));
}

#[test]
fn test_free_variables_bound_excluded() {
    let code = Code::ret(fvar(5));
    let bound = bound_set(&[5]);
    let free = free_variables(&code, &bound);
    assert!(free.is_empty());
}

// ────────────────────────────────────────────────────────────────────────
// closure_convert tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_closure_convert_no_funs() {
    // Code with no local functions should be returned unchanged.
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("x"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );
    let bound = bound_set(&[]);
    let result = closure_convert(&code, &bound);

    assert!(result.closures.is_empty(), "no functions means no closures");
    assert_eq!(result.code, code);
}

#[test]
fn test_closure_convert_fun_with_capture() {
    // let z : Nat := 42
    // fun f (x : Nat) : Nat := let r := z; return r
    // return f
    let code = Code::let_bind(
        LetDecl::new(fvar(50), name("z"), nat_type(), LetValue::nat(42)),
        Code::Fun(
            FunDecl::new(
                fvar(100),
                name("f"),
                vec![Param::new(fvar(1), name("x"), nat_type())],
                nat_type(),
                Code::let_bind(
                    LetDecl::new(
                        fvar(2),
                        name("r"),
                        nat_type(),
                        LetValue::FVar {
                            fvar: fvar(50),
                            args: vec![],
                        },
                    ),
                    Code::ret(fvar(2)),
                ),
            ),
            Box::new(Code::ret(fvar(100))),
        ),
    );

    let bound = bound_set(&[]);
    let result = closure_convert(&code, &bound);

    assert_eq!(
        result.closures.len(),
        1,
        "one local function should produce one closure"
    );
    let env = &result.closures[0];
    assert_eq!(env.capture_count(), 1, "z should be captured");
    assert!(env.find_capture(fvar(50)).is_some(), "z captured");
    assert_eq!(env.param_count, 1, "original param count preserved");
}

#[test]
fn test_closure_convert_nested_funs() {
    // fun f (x) :=
    //   fun g (y) := return x  -- g captures x from f
    //   return g
    // return f
    let inner_fun = FunDecl::new(
        fvar(200),
        name("g"),
        vec![Param::new(fvar(2), name("y"), nat_type())],
        nat_type(),
        Code::ret(fvar(1)), // captures x = fvar(1) from f's params
    );
    let outer_fun = FunDecl::new(
        fvar(100),
        name("f"),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        nat_type(),
        Code::Fun(inner_fun, Box::new(Code::ret(fvar(200)))),
    );
    let code = Code::Fun(outer_fun, Box::new(Code::ret(fvar(100))));

    let bound = bound_set(&[]);
    let result = closure_convert(&code, &bound);

    // Two local functions -> two closures
    assert_eq!(result.closures.len(), 2);
}

#[test]
fn test_closure_convert_preserves_terminal_code() {
    // return x
    let code = Code::ret(fvar(1));
    let bound = bound_set(&[1]);
    let result = closure_convert(&code, &bound);
    assert!(result.closures.is_empty());
    assert_eq!(result.code, code);

    // jmp jp args
    let jmp_code = Code::jmp(fvar(10), vec![Arg::FVar(fvar(1))]);
    let result2 = closure_convert(&jmp_code, &bound);
    assert!(result2.closures.is_empty());
    assert_eq!(result2.code, jmp_code);
}

// ────────────────────────────────────────────────────────────────────────
// capture_types tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_capture_types_lookup() {
    let mut builder = ClosureBuilder::new(fvar(100), 1);
    builder.add_capture(fvar(10), name("a"), 0, CaptureMode::ByValue);
    builder.add_capture(fvar(20), name("b"), 1, CaptureMode::ByValue);
    let env = builder.build();

    let mut type_map = HashMap::new();
    type_map.insert(fvar(10), nat_type());
    type_map.insert(fvar(20), Expr::const_str("Bool"));

    let types = capture_types(&env, &type_map);
    assert_eq!(types.len(), 2);
    assert_eq!(types[0].0, fvar(10));
    assert_eq!(types[1].0, fvar(20));
}

#[test]
fn test_capture_types_missing_type() {
    let mut builder = ClosureBuilder::new(fvar(100), 1);
    builder.add_capture(fvar(10), name("a"), 0, CaptureMode::ByValue);
    let env = builder.build();

    // Empty type map — capture has no known type
    let type_map = HashMap::new();
    let types = capture_types(&env, &type_map);
    assert!(types.is_empty(), "missing types should be filtered out");
}

// ────────────────────────────────────────────────────────────────────────
// ClosureEnv iterator test
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_closure_env_iter() {
    let mut builder = ClosureBuilder::new(fvar(100), 0);
    builder.add_capture(fvar(1), name("a"), 0, CaptureMode::ByValue);
    builder.add_capture(fvar(2), name("b"), 1, CaptureMode::ByRef);
    builder.add_capture(fvar(3), name("c"), 2, CaptureMode::ByValue);
    let env = builder.build();

    let ids: Vec<FVarId> = env.iter().map(|c| c.fvar_id).collect();
    assert_eq!(ids, vec![fvar(1), fvar(2), fvar(3)]);
}

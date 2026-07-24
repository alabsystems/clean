// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interpreter-level tests for `HashMap` / `BTreeMap` iteration and queries.
//!
//! Maps are modeled as a `Value::Struct` whose `entries` field is a
//! `Value::Array` of `(K, V)` 2-tuples. These tests pin that iterating a map
//! (directly, by reference, via `iter()` / `into_iter()`, or via `keys()` /
//! `values()`) materializes those pairs, and that the entry-query methods
//! (`len`, `is_empty`, `contains_key`, `get`) read the same array.

use super::Interpreter;
use crate::expr::{EvalResult, Expr, Pattern, Stmt};
use crate::types::Mutability;
use crate::values::{BinOp, Value};
use std::collections::BTreeMap;

/// Build a `HashMap`-shaped struct value from `(key, value)` integer pairs.
fn map_value(name: &str, pairs: &[(u32, u32)]) -> Value {
    let entries = pairs
        .iter()
        .map(|(k, v)| Value::Tuple(vec![Value::u32(*k), Value::u32(*v)]))
        .collect();
    let mut fields = BTreeMap::new();
    fields.insert("entries".to_string(), Value::Array(entries));
    Value::Struct {
        name: name.to_string(),
        fields,
    }
}

fn var(name: &str) -> Expr {
    Expr::Var {
        name: name.to_string(),
        local_idx: 0,
    }
}

fn let_mut(name: &str, init: Expr) -> Stmt {
    Stmt::Let {
        pattern: Pattern::Binding {
            name: name.to_string(),
            mutable: true,
            subpattern: None,
        },
        ty: None,
        init: Some(Box::new(init)),
        else_block: None,
    }
}

fn add_assign(target: &str, rhs: Expr) -> Stmt {
    Stmt::Expr(Expr::Assign {
        target: Box::new(var(target)),
        value: Box::new(Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(var(target)),
            right: Box::new(rhs),
        }),
    })
}

/// `for (k, v) in &map { sum += k + v }` over a populated map.
#[test]
fn test_for_loop_over_map_ref_sums_keys_and_values() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[(1, 10), (2, 20), (3, 30)]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("map", Expr::Literal(map)),
            let_mut("sum", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Tuple(vec![
                    Pattern::Binding {
                        name: "k".to_string(),
                        mutable: false,
                        subpattern: None,
                    },
                    Pattern::Binding {
                        name: "v".to_string(),
                        mutable: false,
                        subpattern: None,
                    },
                ])),
                iter: Box::new(Expr::AddrOf {
                    mutability: Mutability::Shared,
                    expr: Box::new(var("map")),
                }),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign(
                        "sum",
                        Expr::BinOp {
                            op: BinOp::Add,
                            left: Box::new(var("k")),
                            right: Box::new(var("v")),
                        },
                    )],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("sum"))),
    };
    // (1+10) + (2+20) + (3+30) = 66
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(66)));
}

/// `for (_k, v) in map { sum += v }` consuming the map by value (into_iter).
#[test]
fn test_for_loop_over_map_by_value_sums_values() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[(1, 5), (2, 7)]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("sum", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Tuple(vec![
                    Pattern::Wildcard,
                    Pattern::Binding {
                        name: "v".to_string(),
                        mutable: false,
                        subpattern: None,
                    },
                ])),
                iter: Box::new(Expr::Literal(map)),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign("sum", var("v"))],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("sum"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(12)));
}

/// Iterating an empty map performs no iterations and leaves the accumulator at 0.
#[test]
fn test_for_loop_over_empty_map_yields_no_iterations() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("count", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Tuple(vec![Pattern::Wildcard, Pattern::Wildcard])),
                iter: Box::new(Expr::Literal(map)),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign("count", Expr::Literal(Value::u32(1)))],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("count"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(0)));
}

/// A `BTreeMap` struct iterates exactly like a `HashMap` struct.
#[test]
fn test_for_loop_over_btreemap_ref_iterates_entries() {
    let mut interp = Interpreter::new();
    let map = map_value("BTreeMap", &[(4, 1), (5, 1), (6, 1)]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("map", Expr::Literal(map)),
            let_mut("count", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Tuple(vec![Pattern::Wildcard, Pattern::Wildcard])),
                iter: Box::new(Expr::AddrOf {
                    mutability: Mutability::Shared,
                    expr: Box::new(var("map")),
                }),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign("count", Expr::Literal(Value::u32(1)))],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("count"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(3)));
}

/// `map.values()` yields an array of the stored values; summing it works.
#[test]
fn test_map_values_method_sums_via_for_loop() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[(1, 100), (2, 200), (3, 300)]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("map", Expr::Literal(map)),
            let_mut("sum", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Binding {
                    name: "v".to_string(),
                    mutable: false,
                    subpattern: None,
                }),
                iter: Box::new(Expr::MethodCall {
                    receiver: Box::new(var("map")),
                    method: "values".to_string(),
                    args: vec![],
                    type_args: vec![],
                }),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign("sum", var("v"))],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("sum"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(600)));
}

/// `map.keys()` yields an array of the stored keys; summing it works.
#[test]
fn test_map_keys_method_sums_via_for_loop() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[(1, 0), (2, 0), (4, 0)]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("map", Expr::Literal(map)),
            let_mut("sum", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Binding {
                    name: "k".to_string(),
                    mutable: false,
                    subpattern: None,
                }),
                iter: Box::new(Expr::MethodCall {
                    receiver: Box::new(var("map")),
                    method: "keys".to_string(),
                    args: vec![],
                    type_args: vec![],
                }),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign("sum", var("k"))],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("sum"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(7)));
}

/// `map.iter()` materializes the `(K, V)` pairs and a for-loop counts them.
#[test]
fn test_map_iter_method_counts_entries() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[(1, 1), (2, 2)]);
    let program = Expr::Block {
        stmts: vec![
            let_mut("map", Expr::Literal(map)),
            let_mut("count", Expr::Literal(Value::u32(0))),
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Tuple(vec![Pattern::Wildcard, Pattern::Wildcard])),
                iter: Box::new(Expr::MethodCall {
                    receiver: Box::new(var("map")),
                    method: "iter".to_string(),
                    args: vec![],
                    type_args: vec![],
                }),
                body: Box::new(Expr::Block {
                    stmts: vec![add_assign("count", Expr::Literal(Value::u32(1)))],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("count"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(2)));
}

/// `map.len()` returns the entry count; `is_empty()` reflects emptiness.
#[test]
fn test_map_len_and_is_empty_methods() {
    let mut interp = Interpreter::new();
    let populated = map_value("HashMap", &[(1, 1), (2, 2), (3, 3)]);
    let len_expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(populated)),
        method: "len".to_string(),
        args: vec![],
        type_args: vec![],
    };
    assert_eq!(interp.eval(&len_expr).value(), Some(Value::usize(3)));

    let empty = map_value("HashMap", &[]);
    let is_empty_expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(empty)),
        method: "is_empty".to_string(),
        args: vec![],
        type_args: vec![],
    };
    assert_eq!(interp.eval(&is_empty_expr).value(), Some(Value::Bool(true)));
}

/// `map.contains_key(k)` and `map.get(k)` read the stored entries.
#[test]
fn test_map_contains_key_and_get_methods() {
    let mut interp = Interpreter::new();
    let map = map_value("HashMap", &[(1, 11), (2, 22)]);

    let contains_present = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(map.clone())),
        method: "contains_key".to_string(),
        args: vec![Expr::Literal(Value::u32(2))],
        type_args: vec![],
    };
    assert_eq!(
        interp.eval(&contains_present).value(),
        Some(Value::Bool(true))
    );

    let contains_absent = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(map.clone())),
        method: "contains_key".to_string(),
        args: vec![Expr::Literal(Value::u32(99))],
        type_args: vec![],
    };
    assert_eq!(
        interp.eval(&contains_absent).value(),
        Some(Value::Bool(false))
    );

    let get_present = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(map.clone())),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::u32(1))],
        type_args: vec![],
    };
    assert_eq!(
        interp.eval(&get_present).value(),
        Some(Interpreter::option_value(Some(Value::u32(11))))
    );

    let get_absent = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(map)),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::u32(5))],
        type_args: vec![],
    };
    assert_eq!(
        interp.eval(&get_absent).value(),
        Some(Interpreter::option_value(None))
    );
}

/// Regression guard: a non-map struct is still rejected by the for-loop, so the
/// new HashMap path does not accept arbitrary structs as iterable.
#[test]
fn test_for_loop_over_non_map_struct_is_rejected() {
    let mut interp = Interpreter::new();
    let mut fields = BTreeMap::new();
    fields.insert("x".to_string(), Value::u32(1));
    let strukt = Value::Struct {
        name: "Point".to_string(),
        fields,
    };
    let program = Expr::For {
        label: None,
        pattern: Box::new(Pattern::Wildcard),
        iter: Box::new(Expr::Literal(strukt)),
        body: Box::new(Expr::Block {
            stmts: vec![],
            expr: None,
        }),
    };
    assert!(
        matches!(interp.eval(&program), EvalResult::Error(_)),
        "iterating a non-map struct must remain an error"
    );
}

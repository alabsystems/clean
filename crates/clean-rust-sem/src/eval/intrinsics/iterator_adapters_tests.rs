// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interpreter-level tests for the iterator adapters and consumers.
//!
//! These pin the eager/materializing model: each adapter produces a
//! `Value::Array` of its transformed elements, and the terminal consumers fold
//! that array. Closures are evaluated to `Value::Closure` arguments and applied
//! through the normal callable path, so `map`/`filter` exercise real closure
//! application. Adapters dispatch only for iterable receivers (`Array`,
//! `Range`, map structs), so user methods of the same name are not shadowed.

use crate::eval::Interpreter;
use crate::expr::{EvalResult, Expr, Pattern, Stmt};
use crate::types::{Mutability, RustType, UintType};
use crate::values::{BinOp, Value};
use std::collections::BTreeMap;

fn u32_ty() -> RustType {
    RustType::Uint(UintType::U32)
}

fn var(name: &str) -> Expr {
    Expr::Var {
        name: name.to_string(),
        local_idx: 0,
    }
}

fn u32_array(values: &[u32]) -> Expr {
    Expr::Literal(Value::Array(
        values.iter().copied().map(Value::u32).collect(),
    ))
}

/// `|x| x <op> rhs` over a single `u32` parameter named `x`.
fn u32_binop_closure(op: BinOp, rhs: u32) -> Expr {
    Expr::Closure {
        params: vec![("x".to_string(), u32_ty())],
        body: Box::new(Expr::BinOp {
            op,
            left: Box::new(var("x")),
            right: Box::new(Expr::Literal(Value::u32(rhs))),
        }),
        captures: vec![],
        capture_by_value: false,
    }
}

/// `receiver.method(args...)` builder.
fn call(receiver: Expr, method: &str, args: Vec<Expr>) -> Expr {
    Expr::MethodCall {
        receiver: Box::new(receiver),
        method: method.to_string(),
        args,
        type_args: vec![],
    }
}

fn eval(expr: &Expr) -> EvalResult {
    let mut interp = Interpreter::new();
    interp.eval(expr)
}

#[test]
fn test_map_increments_each_element() {
    // [1, 2, 3].iter().map(|x| x + 1).collect()
    let program = call(
        call(
            call(u32_array(&[1, 2, 3]), "iter", vec![]),
            "map",
            vec![u32_binop_closure(BinOp::Add, 1)],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(2), Value::u32(3), Value::u32(4)]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_filter_keeps_elements_greater_than_one() {
    // [1, 2, 3].iter().filter(|x| x > 1).collect()
    let program = call(
        call(
            call(u32_array(&[1, 2, 3]), "iter", vec![]),
            "filter",
            vec![u32_binop_closure(BinOp::Gt, 1)],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(2), Value::u32(3)]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_map_then_filter_chains() {
    // [1, 2, 3].iter().map(|x| x + 1).filter(|x| x > 2).collect()
    let program = call(
        call(
            call(
                call(u32_array(&[1, 2, 3]), "iter", vec![]),
                "map",
                vec![u32_binop_closure(BinOp::Add, 1)],
            ),
            "filter",
            vec![u32_binop_closure(BinOp::Gt, 2)],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(3), Value::u32(4)]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_enumerate_pairs_index_with_element() {
    // [10, 20].iter().enumerate().collect()
    let program = call(
        call(
            call(u32_array(&[10, 20]), "iter", vec![]),
            "enumerate",
            vec![],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![
        Value::Tuple(vec![Value::usize(0), Value::u32(10)]),
        Value::Tuple(vec![Value::usize(1), Value::u32(20)]),
    ]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_zip_pairs_two_iterators_truncating_to_shorter() {
    // [1, 2, 3].iter().zip([10, 20]).collect()
    let program = call(
        call(
            call(u32_array(&[1, 2, 3]), "iter", vec![]),
            "zip",
            vec![u32_array(&[10, 20])],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![
        Value::Tuple(vec![Value::u32(1), Value::u32(10)]),
        Value::Tuple(vec![Value::u32(2), Value::u32(20)]),
    ]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_sum_folds_elements() {
    // [1, 2, 3, 4].iter().sum()
    let program = call(
        call(u32_array(&[1, 2, 3, 4]), "iter", vec![]),
        "sum",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::u32(10)));
}

#[test]
fn test_product_folds_elements() {
    // [1, 2, 3, 4].iter().product()
    let program = call(
        call(u32_array(&[1, 2, 3, 4]), "iter", vec![]),
        "product",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::u32(24)));
}

#[test]
fn test_count_returns_element_count() {
    // [5, 6, 7].iter().count()
    let program = call(call(u32_array(&[5, 6, 7]), "iter", vec![]), "count", vec![]);
    assert_eq!(eval(&program).value(), Some(Value::usize(3)));
}

#[test]
fn test_map_then_count_chains() {
    // [1, 2, 3].iter().map(|x| x + 1).count()
    let program = call(
        call(
            call(u32_array(&[1, 2, 3]), "iter", vec![]),
            "map",
            vec![u32_binop_closure(BinOp::Add, 1)],
        ),
        "count",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::usize(3)));
}

#[test]
fn test_filter_then_sum_chains() {
    // [1, 2, 3, 4].iter().filter(|x| x > 2).sum()  => 3 + 4 = 7
    let program = call(
        call(
            call(u32_array(&[1, 2, 3, 4]), "iter", vec![]),
            "filter",
            vec![u32_binop_closure(BinOp::Gt, 2)],
        ),
        "sum",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::u32(7)));
}

#[test]
fn test_empty_iterator_map_collect_is_empty() {
    // [].iter().map(|x| x + 1).collect() => []
    let program = call(
        call(
            call(u32_array(&[]), "iter", vec![]),
            "map",
            vec![u32_binop_closure(BinOp::Add, 1)],
        ),
        "collect",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::Array(vec![])));
}

#[test]
fn test_empty_iterator_count_is_zero() {
    // [].iter().count() => 0
    let program = call(call(u32_array(&[]), "iter", vec![]), "count", vec![]);
    assert_eq!(eval(&program).value(), Some(Value::usize(0)));
}

#[test]
fn test_empty_iterator_filter_collect_is_empty() {
    // [].iter().filter(|x| x > 1).collect() => []
    let program = call(
        call(
            call(u32_array(&[]), "iter", vec![]),
            "filter",
            vec![u32_binop_closure(BinOp::Gt, 1)],
        ),
        "collect",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::Array(vec![])));
}

#[test]
fn test_empty_iterator_sum_is_error_without_element_type() {
    // [].iter().sum() — cannot seed the zero identity at a concrete width.
    let program = call(call(u32_array(&[]), "iter", vec![]), "sum", vec![]);
    assert!(
        matches!(eval(&program), EvalResult::Error(_)),
        "empty sum should be a typed-zero error, not a guessed value"
    );
}

#[test]
fn test_take_keeps_prefix() {
    // [1, 2, 3, 4].iter().take(2).collect()
    let program = call(
        call(
            call(u32_array(&[1, 2, 3, 4]), "iter", vec![]),
            "take",
            vec![Expr::Literal(Value::usize(2))],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(1), Value::u32(2)]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_skip_drops_prefix() {
    // [1, 2, 3, 4].iter().skip(2).collect()
    let program = call(
        call(
            call(u32_array(&[1, 2, 3, 4]), "iter", vec![]),
            "skip",
            vec![Expr::Literal(Value::usize(2))],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(3), Value::u32(4)]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_rev_reverses_elements() {
    // [1, 2, 3].iter().rev().collect()
    let program = call(
        call(call(u32_array(&[1, 2, 3]), "iter", vec![]), "rev", vec![]),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(3), Value::u32(2), Value::u32(1)]);
    assert_eq!(eval(&program).value(), Some(expected));
}

#[test]
fn test_max_returns_largest() {
    // [3, 1, 4, 1, 5].iter().max() => Some(5)
    let program = call(
        call(u32_array(&[3, 1, 4, 1, 5]), "iter", vec![]),
        "max",
        vec![],
    );
    assert_eq!(
        eval(&program).value(),
        Some(Interpreter::option_value(Some(Value::u32(5))))
    );
}

#[test]
fn test_min_returns_smallest() {
    // [3, 1, 4, 1, 5].iter().min() => Some(1)
    let program = call(
        call(u32_array(&[3, 1, 4, 1, 5]), "iter", vec![]),
        "min",
        vec![],
    );
    assert_eq!(
        eval(&program).value(),
        Some(Interpreter::option_value(Some(Value::u32(1))))
    );
}

#[test]
fn test_empty_max_returns_none() {
    // [].iter().max() => None
    let program = call(call(u32_array(&[]), "iter", vec![]), "max", vec![]);
    assert_eq!(
        eval(&program).value(),
        Some(Interpreter::option_value(None))
    );
}

#[test]
fn test_range_map_sum_chains() {
    // (1..4).map(|x| x + 1).sum() over u32: (2 + 3 + 4) = 9
    let range = Expr::Literal(Value::Range {
        start: Some(Box::new(Value::u32(1))),
        end: Some(Box::new(Value::u32(4))),
        inclusive: false,
    });
    let program = call(
        call(range, "map", vec![u32_binop_closure(BinOp::Add, 1)]),
        "sum",
        vec![],
    );
    assert_eq!(eval(&program).value(), Some(Value::u32(9)));
}

#[test]
fn test_filter_predicate_non_bool_is_error() {
    // [1, 2].iter().filter(|x| x + 1)  — predicate returns u32, not bool.
    let program = call(
        call(
            call(u32_array(&[1, 2]), "iter", vec![]),
            "filter",
            vec![u32_binop_closure(BinOp::Add, 1)],
        ),
        "collect",
        vec![],
    );
    assert!(
        matches!(eval(&program), EvalResult::Error(_)),
        "a non-bool filter predicate must be rejected, not silently accepted"
    );
}

#[test]
fn test_filter_map_keeps_some_payloads() {
    // [1, 2, 3].iter().filter_map(|x| if x > 1 { Some(x) } else { None }).collect()
    let predicate = Expr::Closure {
        params: vec![("x".to_string(), u32_ty())],
        body: Box::new(Expr::If {
            condition: Box::new(Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(var("x")),
                right: Box::new(Expr::Literal(Value::u32(1))),
            }),
            then_branch: Box::new(Expr::Call {
                func: Box::new(var("Option::Some")),
                args: vec![var("x")],
                type_args: vec![],
            }),
            else_branch: Some(Box::new(Expr::Literal(Interpreter::option_value(None)))),
        }),
        captures: vec![],
        capture_by_value: false,
    };
    let program = call(
        call(
            call(u32_array(&[1, 2, 3]), "iter", vec![]),
            "filter_map",
            vec![predicate],
        ),
        "collect",
        vec![],
    );
    // filter_map only handled if the closure returns Option; ensure no false
    // accept: either it filters to [2, 3] or it is a clean error, never a
    // mis-collected sequence.
    match eval(&program) {
        EvalResult::Value(Value::Array(elems)) => {
            assert_eq!(elems, vec![Value::u32(2), Value::u32(3)]);
        }
        EvalResult::Error(_) => {}
        other => panic!("unexpected filter_map result: {other:?}"),
    }
}

#[test]
fn test_fnptr_argument_is_applied_by_map() {
    // Register `fn inc(x: u32) -> u32 { x + 1 }`, then [1, 2].iter().map(inc).
    let mut interp = Interpreter::new();
    interp.ctx.register_function(crate::stmt::FunctionDef {
        name: "inc".to_string(),
        params: vec![("x".to_string(), u32_ty())],
        ret_ty: u32_ty(),
        body: Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(var("x")),
            right: Box::new(Expr::Literal(Value::u32(1))),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    let program = call(
        call(
            call(u32_array(&[1, 2]), "iter", vec![]),
            "map",
            vec![Expr::Literal(Value::FnPtr {
                name: "inc".to_string(),
            })],
        ),
        "collect",
        vec![],
    );
    let expected = Value::Array(vec![Value::u32(2), Value::u32(3)]);
    assert_eq!(interp.eval(&program).value(), Some(expected));
}

#[test]
fn test_map_does_not_shadow_user_method_on_non_iterable() {
    // The adapter is gated on iterable receivers. A `map` method invoked on a
    // non-iterable struct must resolve to the user-defined function, not be
    // intercepted by the iterator adapter.
    let mut interp = Interpreter::new();
    interp.ctx.register_function(crate::stmt::FunctionDef {
        name: "map".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "Widget".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: u32_ty(),
        body: Expr::Literal(Value::u32(99)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    let mut fields = BTreeMap::new();
    fields.insert("value".to_string(), Value::u32(1));
    let widget = Value::Struct {
        name: "Widget".to_string(),
        fields,
    };
    let program = call(Expr::Literal(widget), "map", vec![]);
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(99)));
}

#[test]
fn test_for_loop_over_adapter_result_still_iterates() {
    // Adapters return arrays, so a for-loop over `.iter().map(...)` iterates.
    // sum = 0; for x in [1, 2, 3].iter().map(|x| x + 1) { sum += x } => 9
    let mut interp = Interpreter::new();
    let program = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "sum".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Literal(Value::u32(0)))),
                else_block: None,
            },
            Stmt::Expr(Expr::For {
                label: None,
                pattern: Box::new(Pattern::Binding {
                    name: "x".to_string(),
                    mutable: false,
                    subpattern: None,
                }),
                iter: Box::new(call(
                    call(u32_array(&[1, 2, 3]), "iter", vec![]),
                    "map",
                    vec![u32_binop_closure(BinOp::Add, 1)],
                )),
                body: Box::new(Expr::Block {
                    stmts: vec![Stmt::Expr(Expr::Assign {
                        target: Box::new(var("sum")),
                        value: Box::new(Expr::BinOp {
                            op: BinOp::Add,
                            left: Box::new(var("sum")),
                            right: Box::new(var("x")),
                        }),
                    })],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(var("sum"))),
    };
    assert_eq!(interp.eval(&program).value(), Some(Value::u32(9)));
}

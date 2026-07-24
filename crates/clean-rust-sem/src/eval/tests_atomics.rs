// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::values::{EnumPayload, Ordering};

fn var(name: &str) -> Expr {
    Expr::Var {
        name: name.to_string(),
        local_idx: 0,
    }
}

fn binding(name: &str) -> Pattern {
    Pattern::Binding {
        name: name.to_string(),
        mutable: false,
        subpattern: None,
    }
}

fn let_stmt(name: &str, init: Expr) -> Stmt {
    Stmt::Let {
        pattern: binding(name),
        ty: None,
        init: Some(Box::new(init)),
        else_block: None,
    }
}

fn ordering(ordering: Ordering) -> Expr {
    Expr::Literal(Value::Ordering(ordering))
}

fn atomic_i32_new(value: i32) -> Expr {
    Expr::Call {
        func: Box::new(Expr::Var {
            name: "AtomicI32::new".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::i32(value))],
        type_args: vec![],
    }
}

fn atomic_function(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call {
        func: Box::new(Expr::Var {
            name: name.to_string(),
            local_idx: 0,
        }),
        args,
        type_args: vec![],
    }
}

fn atomic_method(receiver: &str, method: &str, args: Vec<Expr>) -> Expr {
    Expr::MethodCall {
        receiver: Box::new(var(receiver)),
        method: method.to_string(),
        args,
        type_args: vec![],
    }
}

fn ok(value: Value) -> Value {
    Value::Enum {
        name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![value])),
    }
}

fn err(value: Value) -> Value {
    Value::Enum {
        name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![value])),
    }
}

#[test]
fn test_atomic_i32_new_intrinsic_returns_atomic_value() {
    let mut interp = Interpreter::new();
    let result = interp.eval(&atomic_i32_new(5));
    assert_eq!(
        result.value(),
        Some(Value::Atomic {
            inner: Box::new(Value::i32(5)),
        })
    );
}

#[test]
fn test_atomic_i32_load_and_store_update_value() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            let_stmt("a", atomic_i32_new(1)),
            Stmt::Expr(atomic_method(
                "a",
                "store",
                vec![Expr::Literal(Value::i32(7)), ordering(Ordering::Release)],
            )),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            atomic_method("a", "load", vec![ordering(Ordering::Acquire)]),
            var("a"),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::i32(7),
            Value::Atomic {
                inner: Box::new(Value::i32(7)),
            },
        ]))
    );
}

#[test]
fn test_atomic_i32_fetch_add_and_fetch_sub_return_previous_values() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            let_stmt("a", atomic_i32_new(10)),
            let_stmt(
                "prev_add",
                atomic_method(
                    "a",
                    "fetch_add",
                    vec![Expr::Literal(Value::i32(5)), ordering(Ordering::AcqRel)],
                ),
            ),
            let_stmt(
                "prev_sub",
                atomic_method(
                    "a",
                    "fetch_sub",
                    vec![Expr::Literal(Value::i32(3)), ordering(Ordering::SeqCst)],
                ),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("prev_add"),
            var("prev_sub"),
            atomic_method("a", "load", vec![ordering(Ordering::Relaxed)]),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::i32(10),
            Value::i32(15),
            Value::i32(12),
        ]))
    );
}

#[test]
fn test_atomic_i32_swap_returns_previous_value() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![let_stmt("a", atomic_i32_new(2))],
        expr: Some(Box::new(Expr::Tuple(vec![
            atomic_method(
                "a",
                "swap",
                vec![Expr::Literal(Value::i32(8)), ordering(Ordering::SeqCst)],
            ),
            atomic_method("a", "load", vec![ordering(Ordering::Relaxed)]),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![Value::i32(2), Value::i32(8)]))
    );
}

#[test]
fn test_atomic_i32_fetch_bitwise_ops_return_previous_values() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            let_stmt("a", atomic_i32_new(0b1100)),
            let_stmt(
                "prev_and",
                atomic_method(
                    "a",
                    "fetch_and",
                    vec![
                        Expr::Literal(Value::i32(0b1010)),
                        ordering(Ordering::SeqCst),
                    ],
                ),
            ),
            let_stmt(
                "prev_or",
                atomic_method(
                    "a",
                    "fetch_or",
                    vec![
                        Expr::Literal(Value::i32(0b0011)),
                        ordering(Ordering::SeqCst),
                    ],
                ),
            ),
            let_stmt(
                "prev_xor",
                atomic_method(
                    "a",
                    "fetch_xor",
                    vec![
                        Expr::Literal(Value::i32(0b0101)),
                        ordering(Ordering::SeqCst),
                    ],
                ),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("prev_and"),
            var("prev_or"),
            var("prev_xor"),
            atomic_method("a", "load", vec![ordering(Ordering::Relaxed)]),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::i32(0b1100),
            Value::i32(0b1000),
            Value::i32(0b1011),
            Value::i32(0b1110),
        ]))
    );
}

#[test]
fn test_atomic_i32_compare_exchange_success_updates_value() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            let_stmt("a", atomic_i32_new(9)),
            let_stmt(
                "result",
                atomic_method(
                    "a",
                    "compare_exchange",
                    vec![
                        Expr::Literal(Value::i32(9)),
                        Expr::Literal(Value::i32(12)),
                        ordering(Ordering::AcqRel),
                        ordering(Ordering::Acquire),
                    ],
                ),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("result"),
            atomic_method("a", "load", vec![ordering(Ordering::Relaxed)]),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![ok(Value::i32(9)), Value::i32(12)]))
    );
}

#[test]
fn test_atomic_i32_compare_exchange_failure_keeps_value() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            let_stmt("a", atomic_i32_new(9)),
            let_stmt(
                "result",
                atomic_method(
                    "a",
                    "compare_exchange",
                    vec![
                        Expr::Literal(Value::i32(8)),
                        Expr::Literal(Value::i32(12)),
                        ordering(Ordering::Acquire),
                        ordering(Ordering::Relaxed),
                    ],
                ),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("result"),
            atomic_method("a", "load", vec![ordering(Ordering::Relaxed)]),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![err(Value::i32(9)), Value::i32(9)]))
    );
}

#[test]
fn test_atomic_i32_compare_exchange_weak_behaves_like_compare_exchange() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            let_stmt("a", atomic_i32_new(3)),
            let_stmt(
                "result",
                atomic_method(
                    "a",
                    "compare_exchange_weak",
                    vec![
                        Expr::Literal(Value::i32(3)),
                        Expr::Literal(Value::i32(4)),
                        ordering(Ordering::SeqCst),
                        ordering(Ordering::Relaxed),
                    ],
                ),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("result"),
            atomic_method("a", "load", vec![ordering(Ordering::Relaxed)]),
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![ok(Value::i32(3)), Value::i32(4)]))
    );
}

#[test]
fn test_atomic_load_rejects_release_ordering() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Atomic {
            inner: Box::new(Value::i32(1)),
        })),
        method: "load".to_string(),
        args: vec![ordering(Ordering::Release)],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(matches!(
        result,
        EvalResult::Error(ref msg) if msg.contains("does not permit `Release` ordering")
    ));
}

#[test]
fn test_atomic_compare_exchange_rejects_release_failure_ordering() {
    let mut interp = Interpreter::new();
    let expr = Expr::Block {
        stmts: vec![let_stmt("a", atomic_i32_new(1))],
        expr: Some(Box::new(atomic_method(
            "a",
            "compare_exchange",
            vec![
                Expr::Literal(Value::i32(1)),
                Expr::Literal(Value::i32(2)),
                ordering(Ordering::SeqCst),
                ordering(Ordering::Release),
            ],
        ))),
    };

    let result = interp.eval(&expr);
    assert!(matches!(
        result,
        EvalResult::Error(ref msg) if msg.contains("does not permit `Release` ordering")
    ));
}

#[test]
fn test_atomic_compare_exchange_rejects_failure_ordering_stronger_than_success() {
    let mut interp = Interpreter::new();
    let expr = Expr::Block {
        stmts: vec![let_stmt("a", atomic_i32_new(1))],
        expr: Some(Box::new(atomic_method(
            "a",
            "compare_exchange",
            vec![
                Expr::Literal(Value::i32(1)),
                Expr::Literal(Value::i32(2)),
                ordering(Ordering::Relaxed),
                ordering(Ordering::Acquire),
            ],
        ))),
    };

    let result = interp.eval(&expr);
    assert!(matches!(
        result,
        EvalResult::Error(ref msg)
            if msg.contains("cannot be stronger than success ordering `Relaxed`")
    ));
}

#[test]
fn test_atomic_fence_intrinsic_returns_unit() {
    let mut interp = Interpreter::new();
    let expr = atomic_function("std::sync::atomic::fence", vec![ordering(Ordering::AcqRel)]);
    assert_eq!(interp.eval(&expr).value(), Some(Value::Unit));
}

#[test]
fn test_atomic_compiler_fence_rejects_relaxed_ordering() {
    let mut interp = Interpreter::new();
    let expr = atomic_function(
        "std::sync::atomic::compiler_fence",
        vec![ordering(Ordering::Relaxed)],
    );

    let result = interp.eval(&expr);
    assert!(matches!(
        result,
        EvalResult::Error(ref msg) if msg.contains("does not permit `Relaxed` ordering")
    ));
}

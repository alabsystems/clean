// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_cell_get_set_replace() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let(
                "cell",
                false,
                None,
                call("Cell::new", vec![Expr::Literal(Value::u32(1))]),
            ),
            Stmt::Expr(method(
                var("cell"),
                "set",
                vec![Expr::Literal(Value::u32(2))],
            )),
            make_let(
                "old",
                false,
                None,
                method(var("cell"), "replace", vec![Expr::Literal(Value::u32(3))]),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("old"),
            method(var("cell"), "get", vec![]),
        ]))),
    };

    assert_eq!(
        interp.eval(&block).value(),
        Some(Value::Tuple(vec![Value::u32(2), Value::u32(3)]))
    );
}

#[test]
fn test_refcell_borrow_and_borrow_mut_release_on_scope_exit() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let(
                "cell",
                false,
                None,
                call("RefCell::new", vec![Expr::Literal(Value::u32(10))]),
            ),
            make_let(
                "first",
                false,
                None,
                Expr::Block {
                    stmts: vec![make_let(
                        "shared",
                        false,
                        None,
                        method(var("cell"), "borrow", vec![]),
                    )],
                    expr: Some(Box::new(Expr::Deref(Box::new(var("shared"))))),
                },
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![
                    make_let(
                        "borrowed_mut",
                        false,
                        None,
                        method(var("cell"), "borrow_mut", vec![]),
                    ),
                    Stmt::Expr(Expr::Assign {
                        target: Box::new(Expr::Deref(Box::new(var("borrowed_mut")))),
                        value: Box::new(Expr::Literal(Value::u32(15))),
                    }),
                ],
                expr: None,
            }),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("first"),
            Expr::Block {
                stmts: vec![make_let(
                    "shared_again",
                    false,
                    None,
                    method(var("cell"), "borrow", vec![]),
                )],
                expr: Some(Box::new(Expr::Deref(Box::new(var("shared_again"))))),
            },
        ]))),
    };

    assert_eq!(
        interp.eval(&block).value(),
        Some(Value::Tuple(vec![Value::u32(10), Value::u32(15)]))
    );
}

#[test]
fn test_refcell_borrow_mut_conflict_returns_borrow_error() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let(
                "cell",
                false,
                None,
                call("RefCell::new", vec![Expr::Literal(Value::u32(1))]),
            ),
            make_let("shared", false, None, method(var("cell"), "borrow", vec![])),
        ],
        expr: Some(Box::new(method(var("cell"), "borrow_mut", vec![]))),
    };

    match interp.eval(&block) {
        EvalResult::Error(msg) => {
            assert!(msg.contains("borrow error [refcell_already_borrowed]"));
            assert!(msg.contains("RefCell already borrowed"));
        }
        other => panic!("expected borrow error, got {other:?}"),
    }
}

#[test]
fn test_refcell_value_tracks_shared_borrow_count() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let(
                "cell",
                false,
                None,
                call("RefCell::new", vec![Expr::Literal(Value::u32(7))]),
            ),
            make_let("shared", false, None, method(var("cell"), "borrow", vec![])),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("cell"),
            Expr::Block {
                stmts: vec![make_let(
                    "shared_two",
                    false,
                    None,
                    method(var("cell"), "borrow", vec![]),
                )],
                expr: Some(Box::new(var("cell"))),
            },
            var("cell"),
        ]))),
    };

    match interp.eval(&block).value() {
        Some(Value::Tuple(states)) => {
            assert_eq!(states.len(), 3);
            assert_refcell_state(
                &states[0],
                Value::u32(7),
                RefCellBorrowState::Shared { count: 1 },
            );
            assert_refcell_state(
                &states[1],
                Value::u32(7),
                RefCellBorrowState::Shared { count: 2 },
            );
            assert_refcell_state(
                &states[2],
                Value::u32(7),
                RefCellBorrowState::Shared { count: 1 },
            );
        }
        other => panic!("expected tuple of RefCell states, got {other:?}"),
    }
}

#[test]
fn test_refcell_value_returns_to_unborrowed_after_scope_exit() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let(
                "cell",
                false,
                None,
                call("RefCell::new", vec![Expr::Literal(Value::u32(9))]),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "shared",
                    false,
                    None,
                    method(var("cell"), "borrow", vec![]),
                )],
                expr: None,
            }),
        ],
        expr: Some(Box::new(var("cell"))),
    };

    match interp.eval(&block).value() {
        Some(value) => assert_refcell_state(&value, Value::u32(9), RefCellBorrowState::Unborrowed),
        other => panic!("expected RefCell value, got {other:?}"),
    }
}

#[test]
fn test_refcell_try_borrow_mut_returns_err() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let(
                "cell",
                false,
                None,
                call("RefCell::new", vec![Expr::Literal(Value::u32(1))]),
            ),
            make_let("shared", false, None, method(var("cell"), "borrow", vec![])),
        ],
        expr: Some(Box::new(method(var("cell"), "try_borrow_mut", vec![]))),
    };

    match interp.eval(&block).value() {
        Some(Value::Enum {
            name,
            variant,
            payload,
        }) => {
            assert_eq!(name, "Result");
            assert_eq!(variant, "Err");
            match payload.as_ref() {
                EnumPayload::Tuple(values) => match values.as_slice() {
                    [Value::Struct { name, fields }] => {
                        assert_eq!(name, "BorrowMutError");
                        assert!(fields.is_empty());
                    }
                    other => panic!("expected BorrowMutError payload, got {other:?}"),
                },
                other => panic!("expected tuple payload, got {other:?}"),
            }
        }
        other => panic!("expected Result::Err, got {other:?}"),
    }
}

#[test]
fn test_oncecell_set_and_get_preserve_first_value() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            make_let("cell", false, None, call("OnceCell::new", vec![])),
            make_let(
                "first",
                false,
                None,
                method(var("cell"), "set", vec![Expr::Literal(Value::u32(7))]),
            ),
            make_let(
                "second",
                false,
                None,
                method(var("cell"), "set", vec![Expr::Literal(Value::u32(9))]),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("first"),
            var("second"),
            deref(unwrap(method(var("cell"), "get", vec![]))),
            var("cell"),
        ]))),
    };

    match interp.eval(&block).value() {
        Some(Value::Tuple(values)) => {
            assert_result_ok_unit(&values[0]);
            assert_result_err_value(&values[1], Value::u32(9));
            assert_eq!(values[2], Value::u32(7));
            assert_once_cell_state(&values[3], Some(Value::u32(7)));
        }
        other => panic!("expected tuple result, got {other:?}"),
    }
}

#[test]
fn test_oncelock_get_or_init_runs_initializer_once() {
    let mut interp = Interpreter::new();
    register_nullary_function(&mut interp, "init_one", Value::u32(11));
    register_nullary_function(&mut interp, "init_two", Value::u32(29));

    let block = Expr::Block {
        stmts: vec![
            make_let("lock", false, None, call("OnceLock::new", vec![])),
            make_let(
                "first",
                false,
                None,
                deref(method(var("lock"), "get_or_init", vec![var("init_one")])),
            ),
            make_let(
                "second",
                false,
                None,
                deref(method(var("lock"), "get_or_init", vec![var("init_two")])),
            ),
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            var("first"),
            var("second"),
            var("lock"),
        ]))),
    };

    match interp.eval(&block).value() {
        Some(Value::Tuple(values)) => {
            assert_eq!(values[0], Value::u32(11));
            assert_eq!(values[1], Value::u32(11));
            assert_once_cell_state(&values[2], Some(Value::u32(11)));
        }
        other => panic!("expected tuple result, got {other:?}"),
    }
}

#[test]
fn test_unsafecell_new_wraps_value() {
    let mut interp = Interpreter::new();
    let expr = call("UnsafeCell::new", vec![Expr::Literal(Value::u32(5))]);

    match interp.eval(&expr).value() {
        Some(Value::UnsafeCell { value, .. }) => assert_eq!(*value, Value::u32(5)),
        other => panic!("expected UnsafeCell value, got {other:?}"),
    }
}

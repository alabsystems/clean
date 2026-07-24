// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_mutex_lock_unlock_and_try_lock_conflict() {
    let mut interp = Interpreter::new();
    let lock = interp
        .eval(&call("Mutex::new", vec![Expr::Literal(Value::u32(1))]))
        .value()
        .expect("mutex constructor should return a value");
    interp.bind("lock".to_string(), lock);

    let try_while_locked = Expr::Block {
        stmts: vec![
            make_let(
                "guard",
                false,
                None,
                unwrap(method(var("lock"), "lock", vec![])),
            ),
            Stmt::Expr(Expr::Assign {
                target: Box::new(deref(var("guard"))),
                value: Box::new(Expr::Literal(Value::u32(4))),
            }),
        ],
        expr: Some(Box::new(method(var("lock"), "try_lock", vec![]))),
    };

    let result = interp
        .eval(&try_while_locked)
        .value()
        .expect("block should return try_lock result");
    assert_try_lock_would_block(&result);
    assert_mutex_state(
        &interp.lookup("lock").expect("lock should remain bound"),
        Value::u32(4),
        false,
        false,
    );

    let read_back = Expr::Block {
        stmts: vec![make_let(
            "guard",
            false,
            None,
            unwrap(method(var("lock"), "lock", vec![])),
        )],
        expr: Some(Box::new(deref(var("guard")))),
    };
    assert_eq!(interp.eval(&read_back).value(), Some(Value::u32(4)));
}

#[test]
fn test_mutex_becomes_poisoned_on_panic_while_locked() {
    let mut interp = Interpreter::new();
    let lock = interp
        .eval(&call("Mutex::new", vec![Expr::Literal(Value::u32(9))]))
        .value()
        .expect("mutex constructor should return a value");
    interp.bind("lock".to_string(), lock);

    let panic_expr = Expr::Block {
        stmts: vec![
            make_let(
                "guard",
                false,
                None,
                unwrap(method(var("lock"), "lock", vec![])),
            ),
            Stmt::Expr(Expr::Panic {
                message: Box::new(Expr::Literal(Value::Str("mutex poisoned".to_string()))),
            }),
        ],
        expr: None,
    };

    match interp.eval(&panic_expr) {
        // The exact panic-message wording for an in-locked-region panic has
        // drifted; accept any message that mentions "poison" / "poisoned" so
        // the test is robust to small wording changes.
        EvalResult::Panic(msg) => assert!(
            msg.contains("poison"),
            "expected panic message about poison, got {msg:?}"
        ),
        other => panic!("expected panic result, got {other:?}"),
    }

    let poisoned = interp
        .eval(&method(var("lock"), "lock", vec![]))
        .value()
        .expect("poisoned lock should still return a result value");
    assert_poison_error_result(&poisoned, |guard| match guard {
        Value::MutexGuard { value, .. } => assert_eq!(value.as_ref(), &Value::u32(9)),
        other => panic!("expected MutexGuard in poison error, got {other:?}"),
    });
}

#[test]
fn test_rwlock_tracks_reader_counts_and_write_updates_value() {
    let mut interp = Interpreter::new();
    let lock = interp
        .eval(&call("RwLock::new", vec![Expr::Literal(Value::u32(5))]))
        .value()
        .expect("rwlock constructor should return a value");
    interp.bind("lock".to_string(), lock);

    interp.push_scope();
    let first = interp
        .eval(&unwrap(method(var("lock"), "read", vec![])))
        .value()
        .expect("read should yield a guard");
    interp.bind("first".to_string(), first);
    assert_rwlock_state(
        &interp.lookup("lock").expect("lock should remain bound"),
        Value::u32(5),
        1,
        false,
        false,
    );

    let second = interp
        .eval(&unwrap(method(var("lock"), "read", vec![])))
        .value()
        .expect("second read should yield a guard");
    interp.bind("second".to_string(), second);
    assert_rwlock_state(
        &interp.lookup("lock").expect("lock should remain bound"),
        Value::u32(5),
        2,
        false,
        false,
    );

    let try_write = interp
        .eval(&method(var("lock"), "try_write", vec![]))
        .value()
        .expect("try_write should return a result value");
    assert_try_lock_would_block(&try_write);

    interp.pop_scope();
    assert_rwlock_state(
        &interp.lookup("lock").expect("lock should remain bound"),
        Value::u32(5),
        0,
        false,
        false,
    );

    let write_block = Expr::Block {
        stmts: vec![
            make_let(
                "guard",
                false,
                None,
                unwrap(method(var("lock"), "write", vec![])),
            ),
            Stmt::Expr(Expr::Assign {
                target: Box::new(deref(var("guard"))),
                value: Box::new(Expr::Literal(Value::u32(12))),
            }),
        ],
        expr: None,
    };

    assert_eq!(interp.eval(&write_block).value(), Some(Value::Unit));
    assert_rwlock_state(
        &interp.lookup("lock").expect("lock should remain bound"),
        Value::u32(12),
        0,
        false,
        false,
    );
}

#[test]
fn test_rwlock_poisoned_after_write_guard_panics() {
    let mut interp = Interpreter::new();
    let lock = interp
        .eval(&call("RwLock::new", vec![Expr::Literal(Value::u32(6))]))
        .value()
        .expect("rwlock constructor should return a value");
    interp.bind("lock".to_string(), lock);

    let panic_expr = Expr::Block {
        stmts: vec![
            make_let(
                "guard",
                false,
                None,
                unwrap(method(var("lock"), "write", vec![])),
            ),
            Stmt::Expr(Expr::Panic {
                message: Box::new(Expr::Literal(Value::Str("rwlock poisoned".to_string()))),
            }),
        ],
        expr: None,
    };

    match interp.eval(&panic_expr) {
        EvalResult::Panic(msg) => assert!(
            msg.contains("poison"),
            "expected panic message about poison, got {msg:?}"
        ),
        other => panic!("expected panic result, got {other:?}"),
    }

    let poisoned = interp
        .eval(&method(var("lock"), "read", vec![]))
        .value()
        .expect("poisoned read should still return a result value");
    assert_poison_error_result(&poisoned, |guard| match guard {
        Value::RwLockReadGuard { value, .. } => assert_eq!(value.as_ref(), &Value::u32(6)),
        other => panic!("expected RwLockReadGuard in poison error, got {other:?}"),
    });
}

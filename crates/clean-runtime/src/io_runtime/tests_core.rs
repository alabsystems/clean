// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IO runtime: core monad operations, console, error handling.

use super::*;

// =============================================================================
// Pure
// =============================================================================

#[test]
fn test_execute_pure_unit_returns_unit() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Pure(IoValue::Unit));
    assert_eq!(result.expect("pure unit should succeed"), IoValue::Unit);
}

#[test]
fn test_execute_pure_string_returns_string() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Pure(IoValue::String("hello".into())));
    assert_eq!(
        result.expect("pure string should succeed"),
        IoValue::String("hello".into())
    );
}

#[test]
fn test_execute_pure_nat_returns_nat() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Pure(IoValue::Nat(42)));
    assert_eq!(result.expect("pure nat should succeed"), IoValue::Nat(42));
}

#[test]
fn test_execute_pure_bool_returns_bool() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Pure(IoValue::Bool(true)));
    assert_eq!(
        result.expect("pure bool should succeed"),
        IoValue::Bool(true)
    );
}

#[test]
fn test_execute_pure_int_returns_int() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Pure(IoValue::Int(-42)));
    assert_eq!(result.expect("pure int should succeed"), IoValue::Int(-42));
}

#[test]
fn test_execute_pure_pair_returns_pair() {
    let rt = IoRuntime::new();
    let pair = IoValue::Pair(
        Box::new(IoValue::Nat(1)),
        Box::new(IoValue::String("x".into())),
    );
    let result = rt.execute(IoAction::Pure(pair.clone()));
    assert_eq!(result.expect("pure pair should succeed"), pair);
}

#[test]
fn test_execute_pure_list_returns_list() {
    let rt = IoRuntime::new();
    let list = IoValue::List(vec![IoValue::Nat(1), IoValue::Nat(2), IoValue::Nat(3)]);
    let result = rt.execute(IoAction::Pure(list.clone()));
    assert_eq!(result.expect("pure list should succeed"), list);
}

// =============================================================================
// PrintLn / Print / EPrintLn
// =============================================================================

#[test]
fn test_println_captures_output() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::PrintLn("hello world".into()));
    assert_eq!(result.expect("println should succeed"), IoValue::Unit);
    assert_eq!(rt.stdout_output(), vec!["hello world"]);
}

#[test]
fn test_println_multiple_captures_all() {
    let rt = IoRuntime::new();
    let action = io_seq(
        IoAction::PrintLn("line 1".into()),
        IoAction::PrintLn("line 2".into()),
    );
    let result = rt.execute(action);
    assert_eq!(
        result.expect("chained println should succeed"),
        IoValue::Unit
    );
    assert_eq!(rt.stdout_output(), vec!["line 1", "line 2"]);
}

#[test]
fn test_print_captures_output() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Print("no newline".into()));
    assert_eq!(result.expect("print should succeed"), IoValue::Unit);
    assert_eq!(rt.stdout_output(), vec!["no newline"]);
}

#[test]
fn test_eprintln_captures_to_stderr_buffer() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::EPrintLn("error msg".into()));
    assert_eq!(result.expect("eprintln should succeed"), IoValue::Unit);
    assert!(rt.stdout_output().is_empty(), "stdout should be empty");
    assert_eq!(rt.stderr_output(), vec!["error msg"]);
}

#[test]
fn test_eprintln_and_println_separate_buffers() {
    let rt = IoRuntime::new();
    let action = io_seq(
        IoAction::PrintLn("to stdout".into()),
        IoAction::EPrintLn("to stderr".into()),
    );
    let result = rt.execute(action);
    assert_eq!(result.expect("mixed io should succeed"), IoValue::Unit);
    assert_eq!(rt.stdout_output(), vec!["to stdout"]);
    assert_eq!(rt.stderr_output(), vec!["to stderr"]);
}

// =============================================================================
// Bind
// =============================================================================

#[test]
fn test_bind_chains_values() {
    let rt = IoRuntime::new();
    let action = io_bind(IoAction::Pure(IoValue::Nat(10)), |v| {
        if let IoValue::Nat(n) = v {
            IoAction::Pure(IoValue::Nat(n + 1))
        } else {
            IoAction::Panic("expected Nat".into())
        }
    });
    let result = rt.execute(action);
    assert_eq!(result.expect("bind chain should succeed"), IoValue::Nat(11));
}

#[test]
fn test_bind_three_deep() {
    let rt = IoRuntime::new();
    let action = io_bind(IoAction::Pure(IoValue::Nat(1)), |v1| {
        io_bind(
            IoAction::Pure(IoValue::Nat(if let IoValue::Nat(n) = v1 {
                n + 1
            } else {
                0
            })),
            |v2| {
                IoAction::Pure(IoValue::Nat(if let IoValue::Nat(n) = v2 {
                    n * 10
                } else {
                    0
                }))
            },
        )
    });
    let result = rt.execute(action);
    assert_eq!(
        result.expect("triple bind should succeed"),
        IoValue::Nat(20)
    );
}

#[test]
fn test_bind_println_then_pure() {
    let rt = IoRuntime::new();
    let action = io_bind(IoAction::PrintLn("step 1".into()), |_| {
        IoAction::Pure(IoValue::Nat(99))
    });
    let result = rt.execute(action);
    assert_eq!(result.expect("bind should succeed"), IoValue::Nat(99));
    assert_eq!(rt.stdout_output(), vec!["step 1"]);
}

// =============================================================================
// Map
// =============================================================================

#[test]
fn test_map_transforms_value() {
    let rt = IoRuntime::new();
    let action = io_map(IoAction::Pure(IoValue::Nat(5)), |v| {
        if let IoValue::Nat(n) = v {
            IoValue::String(format!("value={n}"))
        } else {
            IoValue::Unit
        }
    });
    let result = rt.execute(action);
    assert_eq!(
        result.expect("map should succeed"),
        IoValue::String("value=5".into())
    );
}

#[test]
fn test_map_after_side_effect() {
    let rt = IoRuntime::new();
    let action = io_map(IoAction::PrintLn("hello".into()), |_| IoValue::Nat(99));
    let result = rt.execute(action);
    assert_eq!(result.expect("map after println"), IoValue::Nat(99));
    assert_eq!(rt.stdout_output(), vec!["hello"]);
}

// =============================================================================
// Throw / Catch
// =============================================================================

#[test]
fn test_throw_produces_thrown_error() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Throw(IoValue::String("oops".into())));
    let err = result.expect_err("throw should produce error");
    assert!(
        matches!(&err, IoError::Thrown(IoValue::String(s)) if s == "oops"),
        "expected Thrown error, got: {err}"
    );
}

#[test]
fn test_catch_recovers_from_throw() {
    let rt = IoRuntime::new();
    let action = io_catch(IoAction::Throw(IoValue::String("err".into())), |err_val| {
        IoAction::Pure(IoValue::Pair(
            Box::new(IoValue::String("recovered".into())),
            Box::new(err_val),
        ))
    });
    let result = rt.execute(action);
    let expected = IoValue::Pair(
        Box::new(IoValue::String("recovered".into())),
        Box::new(IoValue::String("err".into())),
    );
    assert_eq!(result.expect("catch should recover"), expected);
}

#[test]
fn test_catch_passes_through_success() {
    let rt = IoRuntime::new();
    let action = io_catch(IoAction::Pure(IoValue::Nat(42)), |_| {
        IoAction::Panic("should not be called".into())
    });
    let result = rt.execute(action);
    assert_eq!(
        result.expect("catch should pass through success"),
        IoValue::Nat(42)
    );
}

#[test]
fn test_catch_does_not_catch_panic() {
    let rt = IoRuntime::new();
    let action = io_catch(IoAction::Panic("fatal".into()), |_| {
        IoAction::Pure(IoValue::String("recovered".into()))
    });
    let result = rt.execute(action);
    let err = result.expect_err("panic should not be caught");
    assert!(
        matches!(&err, IoError::Panic(msg) if msg == "fatal"),
        "expected Panic, got: {err}"
    );
}

#[test]
fn test_nested_catch_inner_recovers() {
    let rt = IoRuntime::new();
    let inner = io_catch(
        IoAction::Throw(IoValue::String("inner error".into())),
        |_| IoAction::Pure(IoValue::String("inner recovered".into())),
    );
    let outer = io_catch(inner, |_| {
        IoAction::Pure(IoValue::String("outer recovered".into()))
    });
    let result = rt.execute(outer);
    assert_eq!(
        result.expect("inner catch should handle"),
        IoValue::String("inner recovered".into())
    );
}

#[test]
fn test_throw_in_bind_caught_by_outer_catch() {
    let rt = IoRuntime::new();
    let inner = io_bind(IoAction::PrintLn("before throw".into()), |_| {
        IoAction::Throw(IoValue::String("mid-chain error".into()))
    });
    let action = io_catch(inner, |err| {
        io_bind(IoAction::PrintLn("caught error".into()), move |_| {
            IoAction::Pure(err)
        })
    });
    let result = rt.execute(action);
    assert_eq!(
        result.expect("should recover"),
        IoValue::String("mid-chain error".into())
    );
    assert_eq!(rt.stdout_output(), vec!["before throw", "caught error"]);
}

// =============================================================================
// GetLine (pre-loaded stdin)
// =============================================================================

#[test]
fn test_getline_from_preloaded_stdin() {
    let rt = IoRuntime::with_stdin(vec!["alice".into(), "bob".into()]);
    let action = io_bind(IoAction::GetLine, |first| {
        io_bind(IoAction::GetLine, move |second| {
            IoAction::Pure(IoValue::Pair(Box::new(first), Box::new(second)))
        })
    });
    let result = rt.execute(action);
    let expected = IoValue::Pair(
        Box::new(IoValue::String("alice".into())),
        Box::new(IoValue::String("bob".into())),
    );
    assert_eq!(
        result.expect("getline should return preloaded lines"),
        expected
    );
}

// =============================================================================
// Panic
// =============================================================================

#[test]
fn test_panic_returns_error() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::Panic("something broke".into()));
    let err = result.expect_err("panic should produce IoError");
    assert!(
        matches!(&err, IoError::Panic(msg) if msg == "something broke"),
        "expected Panic error, got: {err}"
    );
}

#[test]
fn test_panic_in_bind_aborts_chain() {
    let rt = IoRuntime::new();
    let action = io_bind(IoAction::Panic("early exit".into()), |_| {
        IoAction::PrintLn("should not run".into())
    });
    let result = rt.execute(action);
    assert!(result.is_err(), "panic in bind should abort");
    assert!(
        rt.stdout_output().is_empty(),
        "continuation after panic should not execute"
    );
}

// =============================================================================
// Convenience constructors / Default
// =============================================================================

#[test]
fn test_io_seq_discards_first_result() {
    let rt = IoRuntime::new();
    let action = io_seq(
        IoAction::PrintLn("side effect".into()),
        IoAction::Pure(IoValue::Nat(42)),
    );
    let result = rt.execute(action);
    assert_eq!(result.expect("seq should succeed"), IoValue::Nat(42));
    assert_eq!(rt.stdout_output(), vec!["side effect"]);
}

#[test]
fn test_io_bind_convenience() {
    let rt = IoRuntime::new();
    let action = io_bind(IoAction::Pure(IoValue::Nat(7)), |v| {
        IoAction::Pure(IoValue::Pair(Box::new(v), Box::new(IoValue::Unit)))
    });
    let result = rt.execute(action);
    assert_eq!(
        result.expect("io_bind should succeed"),
        IoValue::Pair(Box::new(IoValue::Nat(7)), Box::new(IoValue::Unit))
    );
}

#[test]
fn test_default_runtime_is_empty() {
    let rt = IoRuntime::default();
    assert!(rt.stdout_output().is_empty());
    assert!(rt.stderr_output().is_empty());
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;
use crate::values::EnumPayload;

#[test]
fn test_builtin_array_len_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(1),
            Value::u32(2),
            Value::u32(3),
        ]))),
        method: "len".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::usize(3)));
}

#[test]
fn test_builtin_array_is_empty_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(Vec::new()))),
        method: "is_empty".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_array_contains_method_found() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
            Value::u32(30),
        ]))),
        method: "contains".to_string(),
        args: vec![Expr::Literal(Value::u32(20))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_array_contains_method_not_found() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
        ]))),
        method: "contains".to_string(),
        args: vec![Expr::Literal(Value::u32(99))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_builtin_array_first_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
            Value::u32(30),
        ]))),
        method: "first".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(10)])),
        })
    );
}

#[test]
fn test_builtin_array_first_method_empty() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![]))),
        method: "first".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_builtin_array_last_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
            Value::u32(30),
        ]))),
        method: "last".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(30)])),
        })
    );
}

#[test]
fn test_builtin_array_last_method_empty() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![]))),
        method: "last".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_builtin_array_get_method_in_bounds_returns_some() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
            Value::u32(30),
        ]))),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::usize(1))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(20)])),
        })
    );
}

#[test]
fn test_builtin_array_get_method_last_index_returns_some() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
            Value::u32(30),
        ]))),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::usize(2))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(30)])),
        })
    );
}

#[test]
fn test_builtin_array_get_method_out_of_bounds_returns_none() {
    // `slice::get(i)` is the safe, non-panicking alternative to `slice[i]`.
    // An index equal to the length must yield `None`, not a hard error.
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![
            Value::u32(10),
            Value::u32(20),
        ]))),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::usize(2))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_builtin_array_get_method_empty_returns_none() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![]))),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::usize(0))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_builtin_array_get_method_rejects_wrong_arity() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![Value::u32(1)]))),
        method: "get".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `get` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_array_get_method_rejects_non_integer_index() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![Value::u32(1)]))),
        method: "get".to_string(),
        args: vec![Expr::Literal(Value::Bool(true))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "slice::get expects a usize index argument")
    );
}

#[test]
fn test_builtin_first_rejects_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![Value::u32(1)]))),
        method: "first".to_string(),
        args: vec![Expr::Literal(Value::u32(0))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `first` takes 0 args, got 1")
    );
}

#[test]
fn test_builtin_last_rejects_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Array(vec![Value::u32(1)]))),
        method: "last".to_string(),
        args: vec![Expr::Literal(Value::u32(0))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `last` takes 0 args, got 1")
    );
}

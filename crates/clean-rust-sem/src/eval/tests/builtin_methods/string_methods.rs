// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;
use crate::values::EnumPayload;

#[test]
fn test_builtin_string_len_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("clean".to_string()))),
        method: "len".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::usize(5)));
}

#[test]
fn test_builtin_string_len_method_rejects_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("clean".to_string()))),
        method: "len".to_string(),
        args: vec![Expr::Literal(Value::u32(1))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `len` takes 0 args, got 1")
    );
}

#[test]
fn test_builtin_string_is_empty_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("clean".to_string()))),
        method: "is_empty".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_builtin_string_is_empty_method_rejects_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str(String::new()))),
        method: "is_empty".to_string(),
        args: vec![Expr::Literal(Value::u32(1))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `is_empty` takes 0 args, got 1")
    );
}

#[test]
fn test_builtin_string_contains_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hello world".to_string()))),
        method: "contains".to_string(),
        args: vec![Expr::Literal(Value::Str("world".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_string_contains_method_not_found() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hello".to_string()))),
        method: "contains".to_string(),
        args: vec![Expr::Literal(Value::Str("xyz".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_builtin_contains_method_rejects_no_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hi".to_string()))),
        method: "contains".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `contains` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_string_starts_with_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hello world".to_string()))),
        method: "starts_with".to_string(),
        args: vec![Expr::Literal(Value::Str("hello".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_string_starts_with_method_no_match() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hello world".to_string()))),
        method: "starts_with".to_string(),
        args: vec![Expr::Literal(Value::Str("world".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_builtin_string_ends_with_method() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hello world".to_string()))),
        method: "ends_with".to_string(),
        args: vec![Expr::Literal(Value::Str("world".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_string_ends_with_method_no_match() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hello world".to_string()))),
        method: "ends_with".to_string(),
        args: vec![Expr::Literal(Value::Str("hello".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_builtin_starts_with_rejects_no_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hi".to_string()))),
        method: "starts_with".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `starts_with` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_ends_with_rejects_no_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hi".to_string()))),
        method: "ends_with".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `ends_with` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_string_push_str_method_updates_variable() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "s".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Literal(Value::Str("ru".to_string())))),
                else_block: None,
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(Expr::Var {
                    name: "s".to_string(),
                    local_idx: 0,
                }),
                method: "push_str".to_string(),
                args: vec![Expr::Literal(Value::Str("st".to_string()))],
                type_args: vec![],
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "s".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::Str("rust".to_string())));
}

#[test]
fn test_builtin_string_push_method_updates_variable() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "s".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Literal(Value::Str("ru".to_string())))),
                else_block: None,
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(Expr::Var {
                    name: "s".to_string(),
                    local_idx: 0,
                }),
                method: "push".to_string(),
                args: vec![Expr::Literal(Value::Char('s'))],
                type_args: vec![],
            }),
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(Expr::Var {
                    name: "s".to_string(),
                    local_idx: 0,
                }),
                method: "push".to_string(),
                args: vec![Expr::Literal(Value::Char('t'))],
                type_args: vec![],
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "s".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::Str("rust".to_string())));
}

#[test]
fn test_builtin_string_pop_method_updates_variable_and_returns_char() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "s".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Literal(Value::Str("rust".to_string())))),
                else_block: None,
            },
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "last".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Var {
                        name: "s".to_string(),
                        local_idx: 0,
                    }),
                    method: "pop".to_string(),
                    args: vec![],
                    type_args: vec![],
                })),
                else_block: None,
            },
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            Expr::Var {
                name: "last".to_string(),
                local_idx: 0,
            },
            Expr::Var {
                name: "s".to_string(),
                local_idx: 0,
            },
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::Enum {
                name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Box::new(EnumPayload::Tuple(vec![Value::Char('t')])),
            },
            Value::Str("rus".to_string()),
        ]))
    );
}

#[test]
fn test_builtin_string_pop_method_empty_returns_none() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "s".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Literal(Value::Str(String::new())))),
                else_block: None,
            },
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "last".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Var {
                        name: "s".to_string(),
                        local_idx: 0,
                    }),
                    method: "pop".to_string(),
                    args: vec![],
                    type_args: vec![],
                })),
                else_block: None,
            },
        ],
        expr: Some(Box::new(Expr::Tuple(vec![
            Expr::Var {
                name: "last".to_string(),
                local_idx: 0,
            },
            Expr::Var {
                name: "s".to_string(),
                local_idx: 0,
            },
        ]))),
    };

    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::Enum {
                name: "Option".to_string(),
                variant: "None".to_string(),
                payload: Box::new(EnumPayload::Unit),
            },
            Value::Str(String::new()),
        ]))
    );
}

#[test]
fn test_builtin_push_str_rejects_no_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hi".to_string()))),
        method: "push_str".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `push_str` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_push_rejects_non_char_arg() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hi".to_string()))),
        method: "push".to_string(),
        args: vec![Expr::Literal(Value::Str("!".to_string()))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "str::push expects a char argument")
    );
}

#[test]
fn test_builtin_pop_rejects_args() {
    let mut interp = Interpreter::new();
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Str("hi".to_string()))),
        method: "pop".to_string(),
        args: vec![Expr::Literal(Value::Char('!'))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `pop` takes 0 args, got 1")
    );
}

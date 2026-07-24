// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::expr::Pattern;
use crate::memory::{Address, AllocId};
use crate::stacked_borrows::BorrowPermission;
use crate::types::{
    ClosureKind, ConstGenericArg, ConstParamDef, IntType, Lifetime, Mutability, RustType,
    TypeParamDef, UintType,
};
use crate::values::{BinOp, EnumPayload};

mod builtin_methods;

#[test]
fn test_eval_literal() {
    let mut interp = Interpreter::new();
    let expr = Expr::Literal(Value::u32(42));
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_eval_binop_add() {
    let mut interp = Interpreter::new();
    let expr = Expr::BinOp {
        op: BinOp::Add,
        left: Box::new(Expr::Literal(Value::u32(10))),
        right: Box::new(Expr::Literal(Value::u32(20))),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(30)));
}

#[test]
fn test_eval_binop_compare() {
    let mut interp = Interpreter::new();
    let expr = Expr::BinOp {
        op: BinOp::Lt,
        left: Box::new(Expr::Literal(Value::i32(5))),
        right: Box::new(Expr::Literal(Value::i32(10))),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_eval_if_true() {
    let mut interp = Interpreter::new();
    let expr = Expr::If {
        condition: Box::new(Expr::Literal(Value::Bool(true))),
        then_branch: Box::new(Expr::Literal(Value::u32(1))),
        else_branch: Some(Box::new(Expr::Literal(Value::u32(2)))),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_eval_if_false() {
    let mut interp = Interpreter::new();
    let expr = Expr::If {
        condition: Box::new(Expr::Literal(Value::Bool(false))),
        then_branch: Box::new(Expr::Literal(Value::u32(1))),
        else_branch: Some(Box::new(Expr::Literal(Value::u32(2)))),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(2)));
}

#[test]
fn test_eval_let_binding() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: "x".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::u32(42)))),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_eval_tuple() {
    let mut interp = Interpreter::new();
    let expr = Expr::Tuple(vec![
        Expr::Literal(Value::u32(1)),
        Expr::Literal(Value::Bool(true)),
    ]);
    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![Value::u32(1), Value::Bool(true)]))
    );
}

#[test]
fn test_eval_array() {
    let mut interp = Interpreter::new();
    let expr = Expr::Array(vec![
        Expr::Literal(Value::u32(1)),
        Expr::Literal(Value::u32(2)),
        Expr::Literal(Value::u32(3)),
    ]);
    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Array(vec![
            Value::u32(1),
            Value::u32(2),
            Value::u32(3)
        ]))
    );
}

#[test]
fn test_eval_array_index() {
    let mut interp = Interpreter::new();
    let expr = Expr::Index {
        base: Box::new(Expr::Array(vec![
            Expr::Literal(Value::u32(10)),
            Expr::Literal(Value::u32(20)),
            Expr::Literal(Value::u32(30)),
        ])),
        index: Box::new(Expr::Literal(Value::u32(1))),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(20)));
}

#[test]
fn test_eval_struct() {
    let mut interp = Interpreter::new();
    let expr = Expr::Struct {
        name: "Point".to_string(),
        fields: vec![
            ("x".to_string(), Expr::Literal(Value::f64(1.0))),
            ("y".to_string(), Expr::Literal(Value::f64(2.0))),
        ],
        type_args: vec![],
        const_args: vec![],
    };
    let result = interp.eval(&expr);
    match result {
        EvalResult::Value(Value::Struct { name, fields }) => {
            assert_eq!(name, "Point");
            assert_eq!(fields.get("x"), Some(&Value::f64(1.0)));
            assert_eq!(fields.get("y"), Some(&Value::f64(2.0)));
        }
        _ => panic!("expected struct value"),
    }
}

#[test]
fn test_eval_field_access() {
    let mut interp = Interpreter::new();
    let expr = Expr::Field {
        base: Box::new(Expr::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), Expr::Literal(Value::f64(1.0))),
                ("y".to_string(), Expr::Literal(Value::f64(2.0))),
            ],
            type_args: vec![],
            const_args: vec![],
        }),
        field: "y".to_string(),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::f64(2.0)));
}

#[test]
fn test_eval_enum_variant() {
    let mut interp = Interpreter::new();
    let expr = Expr::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: EnumVariantPayload::Tuple(vec![Expr::Literal(Value::u32(42))]),
        type_args: vec![],
        const_args: vec![],
    };
    let result = interp.eval(&expr);
    match result {
        EvalResult::Value(Value::Enum {
            name,
            variant,
            payload,
        }) => {
            assert_eq!(name, "Option");
            assert_eq!(variant, "Some");
            match *payload {
                EnumPayload::Tuple(v) => assert_eq!(v, vec![Value::u32(42)]),
                _ => panic!("expected tuple payload"),
            }
        }
        _ => panic!("expected enum value"),
    }
}

#[test]
fn test_eval_match() {
    let mut interp = Interpreter::new();
    let expr = Expr::Match {
        scrutinee: Box::new(Expr::Literal(Value::u32(2))),
        arms: vec![
            MatchArm {
                pattern: Pattern::Literal(Value::u32(1)),
                guard: None,
                body: Expr::Literal(Value::Bool(false)),
            },
            MatchArm {
                pattern: Pattern::Literal(Value::u32(2)),
                guard: None,
                body: Expr::Literal(Value::Bool(true)),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                guard: None,
                body: Expr::Literal(Value::Bool(false)),
            },
        ],
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_eval_match_binding() {
    let mut interp = Interpreter::new();
    let expr = Expr::Match {
        scrutinee: Box::new(Expr::EnumVariant {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: EnumVariantPayload::Tuple(vec![Expr::Literal(Value::u32(42))]),
            type_args: vec![],
            const_args: vec![],
        }),
        arms: vec![
            MatchArm {
                pattern: Pattern::EnumVariant {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: crate::expr::EnumPatternPayload::Tuple(vec![Pattern::Binding {
                        name: "x".to_string(),
                        mutable: false,
                        subpattern: None,
                    }]),
                },
                guard: None,
                body: Expr::Var {
                    name: "x".to_string(),
                    local_idx: 0,
                },
            },
            MatchArm {
                pattern: Pattern::EnumVariant {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: crate::expr::EnumPatternPayload::Unit,
                },
                guard: None,
                body: Expr::Literal(Value::u32(0)),
            },
        ],
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_eval_while_loop() {
    let mut interp = Interpreter::new();
    // Simple while loop: while true { break }
    let expr = Expr::While {
        label: None,
        condition: Box::new(Expr::Literal(Value::Bool(true))),
        body: Box::new(Expr::Break {
            label: None,
            value: Some(Box::new(Expr::Literal(Value::u32(42)))),
        }),
    };
    let result = interp.eval(&expr);
    // break 42 exits with value 42
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_eval_while_with_condition() {
    let mut interp = Interpreter::new();
    // while false { ... } should return unit immediately
    let expr = Expr::While {
        label: None,
        condition: Box::new(Expr::Literal(Value::Bool(false))),
        body: Box::new(Expr::Literal(Value::u32(999))),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Unit));
}

#[test]
fn test_eval_function_call() {
    let mut interp = Interpreter::new();

    // Define a simple add function
    interp.ctx.register_function(FunctionDef {
        name: "add".to_string(),
        params: vec![
            ("a".to_string(), RustType::Uint(UintType::U32)),
            ("b".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Var {
                name: "a".to_string(),
                local_idx: 0,
            }),
            right: Box::new(Expr::Var {
                name: "b".to_string(),
                local_idx: 1,
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    // Call the function
    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "add".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(10)), Expr::Literal(Value::u32(20))],
        type_args: vec![],
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(30)));
}

#[test]
fn test_eval_recursive_function() {
    let mut interp = Interpreter::new();

    // Define factorial function
    // fn factorial(n: u32) -> u32 {
    //     if n <= 1 { 1 } else { n * factorial(n - 1) }
    // }
    interp.ctx.register_function(FunctionDef {
        name: "factorial".to_string(),
        params: vec![("n".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::If {
            condition: Box::new(Expr::BinOp {
                op: BinOp::Le,
                left: Box::new(Expr::Var {
                    name: "n".to_string(),
                    local_idx: 0,
                }),
                right: Box::new(Expr::Literal(Value::u32(1))),
            }),
            then_branch: Box::new(Expr::Literal(Value::u32(1))),
            else_branch: Some(Box::new(Expr::BinOp {
                op: BinOp::Mul,
                left: Box::new(Expr::Var {
                    name: "n".to_string(),
                    local_idx: 0,
                }),
                right: Box::new(Expr::Call {
                    func: Box::new(Expr::Var {
                        name: "factorial".to_string(),
                        local_idx: 0,
                    }),
                    args: vec![Expr::BinOp {
                        op: BinOp::Sub,
                        left: Box::new(Expr::Var {
                            name: "n".to_string(),
                            local_idx: 0,
                        }),
                        right: Box::new(Expr::Literal(Value::u32(1))),
                    }],
                    type_args: vec![],
                }),
            })),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    // factorial(5) = 120
    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "factorial".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(5))],
        type_args: vec![],
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(120)));
}

#[test]
fn test_eval_return() {
    let mut interp = Interpreter::new();

    // Function with early return
    interp.ctx.register_function(FunctionDef {
        name: "early_return".to_string(),
        params: vec![("n".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Block {
            stmts: vec![Stmt::Expr(Expr::If {
                condition: Box::new(Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(Expr::Var {
                        name: "n".to_string(),
                        local_idx: 0,
                    }),
                    right: Box::new(Expr::Literal(Value::u32(0))),
                }),
                then_branch: Box::new(Expr::Return(Some(Box::new(Expr::Literal(Value::u32(999)))))),
                else_branch: None,
            })],
            expr: Some(Box::new(Expr::Var {
                name: "n".to_string(),
                local_idx: 0,
            })),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    // early_return(0) should return 999
    let expr1 = Expr::Call {
        func: Box::new(Expr::Var {
            name: "early_return".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(0))],
        type_args: vec![],
    };
    assert_eq!(interp.eval(&expr1).value(), Some(Value::u32(999)));

    // early_return(5) should return 5
    let expr2 = Expr::Call {
        func: Box::new(Expr::Var {
            name: "early_return".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(5))],
        type_args: vec![],
    };
    assert_eq!(interp.eval(&expr2).value(), Some(Value::u32(5)));
}

#[test]
fn test_eval_break() {
    let mut interp = Interpreter::new();
    let expr = Expr::Loop {
        label: None,
        body: Box::new(Expr::Break {
            label: None,
            value: Some(Box::new(Expr::Literal(Value::u32(42)))),
        }),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_eval_array_repeat() {
    let mut interp = Interpreter::new();
    let expr = Expr::ArrayRepeat {
        value: Box::new(Expr::Literal(Value::u32(7))),
        count: 4,
    };
    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Array(vec![
            Value::u32(7),
            Value::u32(7),
            Value::u32(7),
            Value::u32(7)
        ]))
    );
}

#[test]
fn test_eval_tuple_field_access() {
    let mut interp = Interpreter::new();
    let expr = Expr::Field {
        base: Box::new(Expr::Tuple(vec![
            Expr::Literal(Value::u32(10)),
            Expr::Literal(Value::u32(20)),
            Expr::Literal(Value::u32(30)),
        ])),
        field: "1".to_string(),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(20)));
}

#[test]
fn test_eval_nested_scope() {
    let mut interp = Interpreter::new();
    // { let x = 1; { let x = 2; x } + x }
    // Inner block should see x=2, outer should see x=1
    let expr = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: "x".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::u32(1)))),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Block {
                stmts: vec![Stmt::Let {
                    pattern: Pattern::Binding {
                        name: "x".to_string(),
                        mutable: false,
                        subpattern: None,
                    },
                    ty: None,
                    init: Some(Box::new(Expr::Literal(Value::u32(2)))),
                    else_block: None,
                }],
                expr: Some(Box::new(Expr::Var {
                    name: "x".to_string(),
                    local_idx: 0,
                })),
            }),
            right: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            }),
        })),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(3))); // 2 + 1 = 3
}

#[test]
fn test_eval_for_loop() {
    let mut interp = Interpreter::new();
    // for x in [1, 2, 3] { sum = sum + x }; sum
    let block = Expr::Block {
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
                iter: Box::new(Expr::Array(vec![
                    Expr::Literal(Value::u32(1)),
                    Expr::Literal(Value::u32(2)),
                    Expr::Literal(Value::u32(3)),
                ])),
                body: Box::new(Expr::Block {
                    stmts: vec![Stmt::Let {
                        pattern: Pattern::Binding {
                            name: "sum".to_string(),
                            mutable: true,
                            subpattern: None,
                        },
                        ty: None,
                        init: Some(Box::new(Expr::BinOp {
                            op: BinOp::Add,
                            left: Box::new(Expr::Var {
                                name: "sum".to_string(),
                                local_idx: 0,
                            }),
                            right: Box::new(Expr::Var {
                                name: "x".to_string(),
                                local_idx: 0,
                            }),
                        })),
                        else_block: None,
                    }],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "sum".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    // With shadowing: sum gets shadowed in each iteration
    // Final outer sum is still 0
    assert_eq!(result.value(), Some(Value::u32(0)));
}

#[test]
fn test_eval_for_loop_over_exclusive_u32_range() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
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
                iter: Box::new(Expr::Range {
                    start: Some(Box::new(Expr::Literal(Value::u32(1)))),
                    end: Some(Box::new(Expr::Literal(Value::u32(4)))),
                    inclusive: false,
                }),
                body: Box::new(Expr::Block {
                    stmts: vec![Stmt::Expr(Expr::Assign {
                        target: Box::new(Expr::Var {
                            name: "sum".to_string(),
                            local_idx: 0,
                        }),
                        value: Box::new(Expr::BinOp {
                            op: BinOp::Add,
                            left: Box::new(Expr::Var {
                                name: "sum".to_string(),
                                local_idx: 0,
                            }),
                            right: Box::new(Expr::Var {
                                name: "x".to_string(),
                                local_idx: 0,
                            }),
                        }),
                    })],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "sum".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::u32(6)));
}

#[test]
fn test_eval_for_loop_over_tuple_with_bool_tail_preserves_tuple_iteration() {
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "count".to_string(),
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
                    name: "value".to_string(),
                    mutable: false,
                    subpattern: None,
                }),
                iter: Box::new(Expr::Literal(Value::Tuple(vec![
                    Value::u32(1),
                    Value::u32(2),
                    Value::Bool(true),
                ]))),
                body: Box::new(Expr::Block {
                    stmts: vec![Stmt::Expr(Expr::Assign {
                        target: Box::new(Expr::Var {
                            name: "count".to_string(),
                            local_idx: 0,
                        }),
                        value: Box::new(Expr::BinOp {
                            op: BinOp::Add,
                            left: Box::new(Expr::Var {
                                name: "count".to_string(),
                                local_idx: 0,
                            }),
                            right: Box::new(Expr::Literal(Value::u32(1))),
                        }),
                    })],
                    expr: None,
                }),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "count".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::u32(3)));
}

#[test]
fn test_eval_cast() {
    let mut interp = Interpreter::new();
    let expr = Expr::Cast {
        expr: Box::new(Expr::Literal(Value::Bool(true))),
        target: RustType::Uint(UintType::U32),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_eval_unop() {
    let mut interp = Interpreter::new();

    // Not
    let expr1 = Expr::UnOp {
        op: crate::values::UnOp::Not,
        expr: Box::new(Expr::Literal(Value::Bool(true))),
    };
    assert_eq!(interp.eval(&expr1).value(), Some(Value::Bool(false)));

    // Neg
    let expr2 = Expr::UnOp {
        op: crate::values::UnOp::Neg,
        expr: Box::new(Expr::Literal(Value::i32(42))),
    };
    assert_eq!(interp.eval(&expr2).value(), Some(Value::i32(-42)));
}

#[test]
fn test_match_with_guard() {
    let mut interp = Interpreter::new();
    let expr = Expr::Match {
        scrutinee: Box::new(Expr::Literal(Value::u32(5))),
        arms: vec![
            MatchArm {
                pattern: Pattern::Binding {
                    name: "x".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                guard: Some(Expr::BinOp {
                    op: BinOp::Lt,
                    left: Box::new(Expr::Var {
                        name: "x".to_string(),
                        local_idx: 0,
                    }),
                    right: Box::new(Expr::Literal(Value::u32(3))),
                }),
                body: Expr::Literal(Value::Bool(false)),
            },
            MatchArm {
                pattern: Pattern::Binding {
                    name: "x".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                guard: None,
                body: Expr::Literal(Value::Bool(true)),
            },
        ],
    };
    let result = interp.eval(&expr);
    // 5 >= 3, so first arm guard fails, second arm matches
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_drop_elaborator_integration() {
    // Test that drop elaborators are properly managed with scopes
    let mut interp = Interpreter::new();

    // Should start with one scope and one drop elaborator
    assert_eq!(interp.bindings.len(), 1);
    assert_eq!(interp.drop_elaborators.len(), 1);

    // Push a new scope
    interp.push_scope();
    assert_eq!(interp.bindings.len(), 2);
    assert_eq!(interp.drop_elaborators.len(), 2);

    // Pop scope
    interp.pop_scope();
    assert_eq!(interp.bindings.len(), 1);
    assert_eq!(interp.drop_elaborators.len(), 1);
}

#[test]
fn test_drop_impl_registration() {
    // Test that Drop implementations can be registered and retrieved
    let mut interp = Interpreter::new();

    // Register a Drop impl for a type
    interp
        .ctx
        .register_drop_impl("MyStruct".to_string(), "MyStruct_drop".to_string());

    // Verify it can be retrieved
    assert_eq!(
        interp.ctx.get_drop_impl("MyStruct"),
        Some(&"MyStruct_drop".to_string())
    );

    // Unknown types should return None
    assert_eq!(interp.ctx.get_drop_impl("UnknownType"), None);
}

#[test]
fn test_schedule_drop() {
    // Test that schedule_drop adds to the current scope's elaborator
    let mut interp = Interpreter::new();

    // Schedule a drop for a non-copy type
    let struct_ty = RustType::Named {
        name: "MyStruct".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };
    let place = Place::Local(42);
    interp.schedule_drop(place.clone(), &struct_ty);

    // The elaborator should have the drop scheduled
    let elaborator = interp.drop_elaborators.last_mut().unwrap();
    let drops = elaborator.drain_drops();
    assert_eq!(drops.len(), 1);
    assert_eq!(drops[0].0, place);
    assert_eq!(drops[0].1, struct_ty);
}

#[test]
fn test_copy_types_not_dropped() {
    // Test that Copy types are not scheduled for dropping
    let mut interp = Interpreter::new();

    // Schedule a drop for a Copy type (u32)
    let copy_ty = RustType::Uint(UintType::U32);
    interp.schedule_drop(Place::Local(99), &copy_ty);

    // Copy types should not be added to drops
    let elaborator = interp.drop_elaborators.last_mut().unwrap();
    let drops = elaborator.drain_drops();
    assert!(drops.is_empty());
}

#[test]
fn test_vtable_dynamic_dispatch() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, VTable};

    let mut interp = Interpreter::new();

    // Register a function that will be the implementation
    let impl_fn = FunctionDef {
        name: "Dog_speak".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "Dog".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(42)), // Returns 42
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Create a VTable for the Animal trait
    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "speak".to_string(),
        "Dog_speak".to_string(),
        FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    // Create a trait object
    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    // Method call on the trait object
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_vtable_missing_method() {
    use crate::types::VTable;

    let mut interp = Interpreter::new();

    // Create a VTable with no methods
    let vtable = VTable::new("Animal".to_string(), "Dog".to_string());

    // Create a trait object
    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    // Method call for non-existent method
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "bark".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(matches!(result, EvalResult::Error(_)));
}

#[test]
fn test_vtable_concrete_type_mismatch() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType, VTable};

    let mut interp = Interpreter::new();

    let impl_fn = FunctionDef {
        name: "Dog_speak".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "Dog".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(1)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "speak".to_string(),
        "Dog_speak".to_string(),
        FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let cat_value = Value::Struct {
        name: "Cat".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(cat_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(msg.contains("concrete type mismatch"));
        }
        _ => panic!("expected type mismatch error"),
    }
}

#[test]
fn test_vtable_receiver_shared_ref_dispatches() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, Mutability, ReceiverMode, VTable};

    let mut interp = Interpreter::new();

    // `fn speak(&self) -> u32` — the impl receives `self: &Dog`.
    let impl_fn = FunctionDef {
        name: "Dog_speak".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }),
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(7)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "speak".to_string(),
        "Dog_speak".to_string(),
        FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::u32(7)),
        "&self trait-object dispatch should call the impl through a shared reference"
    );
}

#[test]
fn test_vtable_receiver_mut_ref_dispatches() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, Mutability, ReceiverMode, VTable};

    let mut interp = Interpreter::new();

    // `fn wag(&mut self) -> u32` — the impl receives `self: &mut Dog`.
    let impl_fn = FunctionDef {
        name: "Dog_wag".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Mutable,
                inner: Box::new(RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }),
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(9)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "wag".to_string(),
        "Dog_wag".to_string(),
        FunctionSignature {
            name: "wag".to_string(),
            receiver: ReceiverMode::ByMut,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "wag".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::u32(9)),
        "&mut self trait-object dispatch should call the impl through a mutable reference"
    );
}

#[test]
fn test_vtable_dispatch_with_arguments() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, VTable};

    let mut interp = Interpreter::new();

    // Register a function that adds its arguments
    // fn Dog_add(self: Dog, x: u32, y: u32) -> u32 { x + y }
    let impl_fn = FunctionDef {
        name: "Dog_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Uint(UintType::U32)),
            ("y".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        // Body: x + y (uses bound parameters)
        body: Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 1,
            }),
            right: Box::new(Expr::Var {
                name: "y".to_string(),
                local_idx: 2,
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Create a VTable with the add method
    let mut vtable = VTable::new("Calculator".to_string(), "Dog".to_string());
    vtable.add_method(
        "add".to_string(),
        "Dog_add".to_string(),
        FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Uint(UintType::U32), RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    // Create a trait object
    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    // Method call: trait_obj.add(10, 32)
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(10)), Expr::Literal(Value::u32(32))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_vtable_dispatch_argument_order() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, RustType, VTable};

    let mut interp = Interpreter::new();

    // Implementation uses self.age - delta to validate argument order.
    let impl_fn = FunctionDef {
        name: "Dog_adjust".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            (
                "delta".to_string(),
                RustType::Int(crate::types::IntType::I32),
            ),
        ],
        ret_ty: RustType::Int(crate::types::IntType::I32),
        body: Expr::BinOp {
            op: BinOp::Sub,
            left: Box::new(Expr::Field {
                base: Box::new(Expr::Var {
                    name: "self".to_string(),
                    local_idx: 0,
                }),
                field: "age".to_string(),
            }),
            right: Box::new(Expr::Var {
                name: "delta".to_string(),
                local_idx: 1,
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "adjust".to_string(),
        "Dog_adjust".to_string(),
        FunctionSignature {
            name: "adjust".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Int(crate::types::IntType::I32)],
            ret: RustType::Int(crate::types::IntType::I32),
            is_async: false,
            type_params: vec![],
        },
    );

    let mut fields = BTreeMap::new();
    fields.insert("age".to_string(), Value::i32(50));
    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields,
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "adjust".to_string(),
        args: vec![Expr::Literal(Value::i32(8))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::i32(42)));
}

#[test]
fn test_vtable_signature_arg_mismatch() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, VTable};

    let mut interp = Interpreter::new();

    let impl_fn = FunctionDef {
        name: "Dog_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Uint(UintType::U32)),
            ("y".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(0)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Calculator".to_string(), "Dog".to_string());
    vtable.add_method(
        "add".to_string(),
        "Dog_add".to_string(),
        FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Uint(UintType::U32), RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(1))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(msg.contains("expects 2 args"));
        }
        _ => panic!("expected argument mismatch error"),
    }
}

#[test]
fn test_static_trait_method_resolution() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definition
    interp.ctx.register_trait_def(
        "Foo".to_string(),
        vec![FunctionSignature {
            name: "bar".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // Register a trait impl: impl Foo for S { fn bar(&self) -> u32 { 42 } }
    // The implementing function name is "S_Foo_bar"
    let impl_fn = FunctionDef {
        name: "S_Foo_bar".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(42)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Register the trait implementation
    interp.ctx.register_trait_impl(
        "Foo".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("Foo", "S", "bar".to_string(), "S_Foo_bar".to_string());

    // Create instance s = S {}
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    // Call s.bar() - should resolve through trait impl
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "bar".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_inherent_method_takes_precedence() {
    use crate::stmt::FunctionDef;
    use crate::types::UintType;

    let mut interp = Interpreter::new();

    // Register an inherent method directly named "bar"
    let inherent_fn = FunctionDef {
        name: "bar".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(100)), // Returns 100
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(inherent_fn);

    // Also register a trait impl with the same method name
    let trait_impl_fn = FunctionDef {
        name: "S_Foo_bar".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(42)), // Returns 42
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(trait_impl_fn);

    interp.ctx.register_trait_impl(
        "Foo".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("Foo", "S", "bar".to_string(), "S_Foo_bar".to_string());

    // Create instance
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    // Call s.bar() - should use inherent method (100), not trait impl (42)
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "bar".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    // Inherent method takes precedence
    assert_eq!(result.value(), Some(Value::u32(100)));
}

#[test]
fn test_method_not_found_error() {
    let mut interp = Interpreter::new();

    // Create instance without any methods registered
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    // Call s.unknown_method() - should error
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "unknown_method".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("undefined method"),
                "should mention undefined method"
            );
            assert!(msg.contains("unknown_method"), "should include method name");
            assert!(msg.contains("S"), "should include type name for debugging");
        }
        _ => panic!("expected undefined method error"),
    }
}

#[test]
fn test_static_trait_method_with_args() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definition
    interp.ctx.register_trait_def(
        "Add".to_string(),
        vec![FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![RustType::Uint(UintType::U32), RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // impl Add for S { fn add(&self, x: u32, y: u32) -> u32 { x + y } }
    let impl_fn = FunctionDef {
        name: "S_Add_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "S".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Uint(UintType::U32)),
            ("y".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        // Body: x + y (using args by position in bindings)
        body: Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            }),
            right: Box::new(Expr::Var {
                name: "y".to_string(),
                local_idx: 0,
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    interp.ctx.register_trait_impl(
        "Add".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("Add", "S", "add".to_string(), "S_Add_add".to_string());

    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    // Call s.add(10, 32) -> should return 42
    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(10)), Expr::Literal(Value::u32(32))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_multiple_traits_on_same_type() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definitions
    interp.ctx.register_trait_def(
        "Foo".to_string(),
        vec![FunctionSignature {
            name: "foo".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );
    interp.ctx.register_trait_def(
        "Bar".to_string(),
        vec![FunctionSignature {
            name: "bar".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // impl Foo for S { fn foo(&self) -> u32 { 1 } }
    let foo_fn = FunctionDef {
        name: "S_Foo_foo".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(1)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(foo_fn);

    // impl Bar for S { fn bar(&self) -> u32 { 2 } }
    let bar_fn = FunctionDef {
        name: "S_Bar_bar".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(2)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(bar_fn);

    // Register both trait impls
    interp.ctx.register_trait_impl(
        "Foo".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("Foo", "S", "foo".to_string(), "S_Foo_foo".to_string());

    interp.ctx.register_trait_impl(
        "Bar".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("Bar", "S", "bar".to_string(), "S_Bar_bar".to_string());

    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    // Call s.foo() -> 1
    let foo_expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value.clone())),
        method: "foo".to_string(),
        args: vec![],
        type_args: vec![],
    };
    let foo_result = interp.eval(&foo_expr);
    assert_eq!(foo_result.value(), Some(Value::u32(1)));

    // Call s.bar() -> 2
    let bar_expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "bar".to_string(),
        args: vec![],
        type_args: vec![],
    };
    let bar_result = interp.eval(&bar_expr);
    assert_eq!(bar_result.value(), Some(Value::u32(2)));
}

#[test]
fn test_vtable_impl_param_count_mismatch() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType, VTable};

    let mut interp = Interpreter::new();

    // Impl has 2 params (self + x), but trait expects 3 (self + x + y)
    let impl_fn = FunctionDef {
        name: "Dog_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(0)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Calculator".to_string(), "Dog".to_string());
    vtable.add_method(
        "add".to_string(),
        "Dog_add".to_string(),
        FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByValue,
            // Trait expects 2 params: x and y
            params: vec![RustType::Uint(UintType::U32), RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(1)), Expr::Literal(Value::u32(2))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("impl method") && msg.contains("params"),
                "expected param count mismatch error, got: {}",
                msg
            );
        }
        _ => panic!("expected param count mismatch error"),
    }
}

#[test]
fn test_vtable_impl_param_type_mismatch() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, IntType, ReceiverMode, UintType, VTable};

    let mut interp = Interpreter::new();

    // Impl has param type i32, but trait expects u32
    let impl_fn = FunctionDef {
        name: "Dog_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Dog".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Int(IntType::I32)), // i32, not u32
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(0)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Calculator".to_string(), "Dog".to_string());
    vtable.add_method(
        "add".to_string(),
        "Dog_add".to_string(),
        FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Uint(UintType::U32)], // Trait expects u32
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(1))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("impl method") && msg.contains("param"),
                "expected param type mismatch error, got: {}",
                msg
            );
        }
        _ => panic!("expected param type mismatch error"),
    }
}

#[test]
fn test_vtable_impl_return_type_mismatch() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, IntType, ReceiverMode, UintType, VTable};

    let mut interp = Interpreter::new();

    // Impl returns i32, but trait expects u32
    let impl_fn = FunctionDef {
        name: "Dog_speak".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "Dog".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Int(IntType::I32), // Returns i32, not u32
        body: Expr::Literal(Value::i32(42)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "speak".to_string(),
        "Dog_speak".to_string(),
        FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32), // Trait expects u32
            is_async: false,
            type_params: vec![],
        },
    );

    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let trait_obj = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Static,
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("impl method") && msg.contains("returns"),
                "expected return type mismatch error, got: {}",
                msg
            );
        }
        _ => panic!("expected return type mismatch error"),
    }
}

#[test]
fn test_trait_object_lifetime_tracking() {
    use crate::types::{FunctionSignature, Lifetime, ReceiverMode, UintType, VTable};

    // Create a trait object with Static lifetime
    let dog_value = Value::Struct {
        name: "Dog".to_string(),
        fields: BTreeMap::new(),
    };
    let mut vtable = VTable::new("Animal".to_string(), "Dog".to_string());
    vtable.add_method(
        "speak".to_string(),
        "Dog_speak".to_string(),
        FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        },
    );

    let trait_obj_static = Value::TraitObject {
        data: Box::new(dog_value.clone()),
        vtable: vtable.clone(),
        lifetime: Lifetime::Static,
    };

    // Verify get_type returns the correct lifetime
    let ty = trait_obj_static.get_type();
    match ty {
        RustType::DynTrait {
            trait_name,
            auto_traits,
        } => {
            assert_eq!(trait_name, "Animal");
            assert!(auto_traits.is_empty());
        }
        _ => panic!("expected DynTrait type"),
    }

    // Create a trait object with a named lifetime
    let trait_obj_named = Value::TraitObject {
        data: Box::new(dog_value),
        vtable,
        lifetime: Lifetime::Named("a".to_string()),
    };

    let ty = trait_obj_named.get_type();
    match ty {
        RustType::DynTrait {
            trait_name,
            auto_traits,
        } => {
            assert_eq!(trait_name, "Animal");
            assert!(auto_traits.is_empty());
        }
        _ => panic!("expected DynTrait type"),
    }
}

#[test]
fn test_static_dispatch_signature_validation_param_count() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definition with signature expecting 2 params (+ self)
    interp.ctx.register_trait_def(
        "Calculator".to_string(),
        vec![FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Uint(UintType::U32), RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // Impl has wrong param count: only 1 param (+ self) instead of 2
    let impl_fn = FunctionDef {
        name: "S_Calculator_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "S".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(0)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Register trait impl
    interp.ctx.register_trait_impl(
        "Calculator".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp.ctx.add_impl_method(
        "Calculator",
        "S",
        "add".to_string(),
        "S_Calculator_add".to_string(),
    );

    // Create instance and call method
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(1)), Expr::Literal(Value::u32(2))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("impl method") && msg.contains("params"),
                "expected param count mismatch error, got: {}",
                msg
            );
        }
        _ => panic!("expected param count mismatch error"),
    }
}

#[test]
fn test_static_dispatch_signature_validation_param_type() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, IntType, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definition with u32 param
    interp.ctx.register_trait_def(
        "Calculator".to_string(),
        vec![FunctionSignature {
            name: "process".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // Impl has wrong param type: i32 instead of u32
    let impl_fn = FunctionDef {
        name: "S_Calculator_process".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "S".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Int(IntType::I32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(0)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Register trait impl
    interp.ctx.register_trait_impl(
        "Calculator".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp.ctx.add_impl_method(
        "Calculator",
        "S",
        "process".to_string(),
        "S_Calculator_process".to_string(),
    );

    // Create instance and call method
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "process".to_string(),
        args: vec![Expr::Literal(Value::u32(42))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("impl method") && msg.contains("type"),
                "expected param type mismatch error, got: {}",
                msg
            );
        }
        _ => panic!("expected param type mismatch error"),
    }
}

#[test]
fn test_static_dispatch_signature_validation_return_type() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, IntType, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definition expecting u32 return type
    interp.ctx.register_trait_def(
        "Calculator".to_string(),
        vec![FunctionSignature {
            name: "compute".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // Impl has wrong return type: i32 instead of u32
    let impl_fn = FunctionDef {
        name: "S_Calculator_compute".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Int(IntType::I32), // Wrong return type
        body: Expr::Literal(Value::i32(0)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Register trait impl
    interp.ctx.register_trait_impl(
        "Calculator".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp.ctx.add_impl_method(
        "Calculator",
        "S",
        "compute".to_string(),
        "S_Calculator_compute".to_string(),
    );

    // Create instance and call method
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "compute".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("impl method") && msg.contains("returns"),
                "expected return type mismatch error, got: {}",
                msg
            );
        }
        _ => panic!("expected return type mismatch error"),
    }
}

#[test]
fn test_static_dispatch_signature_validation_ref_self_param() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode};

    let mut interp = Interpreter::new();
    let concrete_self = RustType::Named {
        name: "S".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };

    interp.ctx.register_trait_def(
        "Comparator".to_string(),
        vec![FunctionSignature {
            name: "same".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Reference {
                lifetime: Lifetime::Static,
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Named {
                    name: "Self".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }),
            }],
            ret: RustType::Bool,
            is_async: false,
            type_params: vec![],
        }],
    );

    let impl_fn = FunctionDef {
        name: "S_Comparator_same".to_string(),
        params: vec![
            ("self".to_string(), concrete_self.clone()),
            (
                "other".to_string(),
                RustType::Reference {
                    lifetime: Lifetime::Static,
                    mutability: Mutability::Shared,
                    inner: Box::new(concrete_self.clone()),
                },
            ),
        ],
        ret_ty: RustType::Bool,
        body: Expr::Literal(Value::Bool(true)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    interp
        .ctx
        .register_trait_impl("Comparator".to_string(), concrete_self);
    interp.ctx.add_impl_method(
        "Comparator",
        "S",
        "same".to_string(),
        "S_Comparator_same".to_string(),
    );

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Struct {
            name: "S".to_string(),
            fields: BTreeMap::new(),
        })),
        method: "same".to_string(),
        args: vec![Expr::Literal(Value::Reference {
            addr: Address::new(AllocId(1), 0),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: None,
        })],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_field_access_autoderefs_preserved_reference_payload() {
    let mut interp = Interpreter::new();
    let mut fields = BTreeMap::new();
    fields.insert("value".to_string(), Value::u32(42));

    let expr = Expr::Field {
        base: Box::new(Expr::Literal(Value::Reference {
            addr: Address::new(AllocId(1), 0),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Some(Box::new(Value::Struct {
                name: "Counter".to_string(),
                fields,
            })),
        })),
        field: "value".to_string(),
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_static_dispatch_signature_validation_option_self_return() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode};
    use crate::values::EnumPayload;

    let mut interp = Interpreter::new();
    let concrete_self = RustType::Named {
        name: "S".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };
    let self_placeholder = RustType::Named {
        name: "Self".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };

    interp.ctx.register_trait_def(
        "Cloner".to_string(),
        vec![FunctionSignature {
            name: "wrap".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Option {
                inner: Box::new(self_placeholder),
            },
            is_async: false,
            type_params: vec![],
        }],
    );

    let receiver_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };
    let wrapped_value = Value::Enum {
        name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![receiver_value.clone()])),
    };
    let impl_fn = FunctionDef {
        name: "S_Cloner_wrap".to_string(),
        params: vec![("self".to_string(), concrete_self.clone())],
        ret_ty: RustType::Option {
            inner: Box::new(concrete_self.clone()),
        },
        body: Expr::Literal(wrapped_value.clone()),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    interp
        .ctx
        .register_trait_impl("Cloner".to_string(), concrete_self);
    interp.ctx.add_impl_method(
        "Cloner",
        "S",
        "wrap".to_string(),
        "S_Cloner_wrap".to_string(),
    );

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(receiver_value)),
        method: "wrap".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(wrapped_value));
}

#[test]
fn test_static_dispatch_valid_signature_passes() {
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definition
    interp.ctx.register_trait_def(
        "Calculator".to_string(),
        vec![FunctionSignature {
            name: "add".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![RustType::Uint(UintType::U32), RustType::Uint(UintType::U32)],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // Impl has correct signature
    let impl_fn = FunctionDef {
        name: "S_Calculator_add".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "S".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            ("x".to_string(), RustType::Uint(UintType::U32)),
            ("y".to_string(), RustType::Uint(UintType::U32)),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 1,
            }),
            right: Box::new(Expr::Var {
                name: "y".to_string(),
                local_idx: 2,
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(impl_fn);

    // Register trait impl
    interp.ctx.register_trait_impl(
        "Calculator".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp.ctx.add_impl_method(
        "Calculator",
        "S",
        "add".to_string(),
        "S_Calculator_add".to_string(),
    );

    // Create instance and call method
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "add".to_string(),
        args: vec![Expr::Literal(Value::u32(3)), Expr::Literal(Value::u32(4))],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_ambiguous_trait_methods_returns_one() {
    // Test that when a type implements multiple traits with the same method name,
    // resolution still succeeds (returns one of them arbitrarily).
    // This tests the documented behavior in resolve_trait_method_with_info.
    use crate::stmt::FunctionDef;
    use crate::types::{FunctionSignature, ReceiverMode, UintType};

    let mut interp = Interpreter::new();

    // Register trait definitions
    interp.ctx.register_trait_def(
        "A".to_string(),
        vec![FunctionSignature {
            name: "do_thing".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );
    interp.ctx.register_trait_def(
        "B".to_string(),
        vec![FunctionSignature {
            name: "do_thing".to_string(),
            receiver: ReceiverMode::ByRef,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    );

    // Register two traits with the same method name "do_thing"
    // Trait A: fn do_thing(&self) -> u32 { returns 1 }
    let a_fn = FunctionDef {
        name: "S_A_do_thing".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(1)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(a_fn);

    // Trait B: fn do_thing(&self) -> u32 { returns 2 }
    let b_fn = FunctionDef {
        name: "S_B_do_thing".to_string(),
        params: vec![(
            "self".to_string(),
            RustType::Named {
                name: "S".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(2)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    };
    interp.ctx.register_function(b_fn);

    // Register both trait impls for type S
    interp.ctx.register_trait_impl(
        "A".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("A", "S", "do_thing".to_string(), "S_A_do_thing".to_string());

    interp.ctx.register_trait_impl(
        "B".to_string(),
        RustType::Named {
            name: "S".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp
        .ctx
        .add_impl_method("B", "S", "do_thing".to_string(), "S_B_do_thing".to_string());

    // Create instance and call ambiguous method
    let s_value = Value::Struct {
        name: "S".to_string(),
        fields: BTreeMap::new(),
    };

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(s_value)),
        method: "do_thing".to_string(),
        args: vec![],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    // Result should be either 1 or 2 (non-deterministic), but should NOT error
    match result {
        EvalResult::Value(v) => {
            let val = v.as_u64().unwrap() as u32;
            assert!(val == 1 || val == 2, "expected 1 or 2, got {}", val);
        }
        EvalResult::Error(e) => panic!("expected value, got error: {}", e),
        _ => panic!("expected value result"),
    }
}

// =========================================================================
// Unsafe block tracking tests
// =========================================================================

#[test]
fn test_unsafe_block_basic() {
    let mut interp = Interpreter::new();

    // Code inside unsafe block should execute normally
    let expr = Expr::Unsafe {
        block: Box::new(Expr::Literal(Value::u32(42))),
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_unsafe_context_tracking() {
    let mut interp = Interpreter::new();

    // Outside unsafe, in_unsafe should be false
    assert!(!interp.ctx.is_unsafe());

    // require_unsafe should fail outside unsafe context
    let err = interp.ctx.require_unsafe("test operation").unwrap_err();
    assert!(
        err.to_string().contains("unsafe"),
        "expected unsafe-related error, got: {err}"
    );

    // Inside unsafe block...
    let was_unsafe = interp.ctx.enter_unsafe();
    assert!(interp.ctx.is_unsafe());
    interp
        .ctx
        .require_unsafe("test operation")
        .expect("require_unsafe should succeed inside unsafe block");
    interp.ctx.exit_unsafe(was_unsafe);

    // Back to safe
    assert!(!interp.ctx.is_unsafe());
}

#[test]
fn test_raw_deref_requires_unsafe() {
    use crate::memory::Address;

    let mut interp = Interpreter::new();

    // Create a raw pointer value
    let ptr = Value::RawPtr {
        addr: Address {
            alloc_id: AllocId(1),
            offset: 0,
        },
        mutability: Mutability::Shared,
        tag: None,
    };

    // Raw dereference outside unsafe should error
    let expr = Expr::RawDeref(Box::new(Expr::Literal(ptr.clone())));
    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(e) => {
            assert!(
                e.contains("unsafe"),
                "error should mention unsafe requirement: {e}"
            );
        }
        _ => panic!("expected error for raw deref outside unsafe"),
    }

    // Inside unsafe block, raw deref should be allowed (but may fail for other reasons)
    let expr_in_unsafe = Expr::Unsafe {
        block: Box::new(Expr::RawDeref(Box::new(Expr::Literal(ptr)))),
    };
    let result = interp.eval(&expr_in_unsafe);
    if let EvalResult::Error(e) = result {
        // Should NOT error about unsafe requirement
        assert!(
            !e.contains("requires an unsafe"),
            "should not error about unsafe requirement: {e}"
        );
    }
    // Other results are fine for this test
}

#[test]
fn test_nested_unsafe_blocks() {
    let mut interp = Interpreter::new();

    // Nested unsafe blocks should work correctly
    let expr = Expr::Unsafe {
        block: Box::new(Expr::Block {
            stmts: vec![],
            expr: Some(Box::new(Expr::Unsafe {
                block: Box::new(Expr::Literal(Value::u32(123))),
            })),
        }),
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(123)));
}

// =========================================================================
// Union type tests
// =========================================================================

#[test]
fn test_union_init() {
    let mut interp = Interpreter::new();

    // Initialize a union with one field
    let expr = Expr::UnionInit {
        name: "MyUnion".to_string(),
        field: ("f1".to_string(), Box::new(Expr::Literal(Value::u32(42)))),
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Value(Value::Union {
            name,
            active_field,
            value,
        }) => {
            assert_eq!(name, "MyUnion");
            assert_eq!(active_field, "f1");
            assert_eq!(*value, Value::u32(42));
        }
        other => panic!("expected union value, got {:?}", other),
    }
}

#[test]
fn test_closure_returning_union_infers_union_type() {
    let mut interp = Interpreter::new();

    let closure = Expr::Closure {
        params: vec![],
        body: Box::new(Expr::UnionInit {
            name: "MyUnion".to_string(),
            field: ("f1".to_string(), Box::new(Expr::Literal(Value::u32(42)))),
        }),
        captures: vec![],
        capture_by_value: false,
    };

    let result = interp.eval(&closure);
    match result {
        EvalResult::Value(Value::Closure { ret_type, .. }) => {
            assert_eq!(
                ret_type,
                RustType::Named {
                    name: "MyUnion".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }
            );
        }
        other => panic!("expected closure value, got {:?}", other),
    }
}

#[test]
fn test_move_closure_with_captures_is_fnonce() {
    let mut interp = Interpreter::new();
    interp.bind("captured".to_string(), Value::u32(42));

    let closure = Expr::Closure {
        params: vec![],
        body: Box::new(Expr::Var {
            name: "captured".to_string(),
            local_idx: 0,
        }),
        captures: vec![("captured".to_string(), Mutability::Shared)],
        capture_by_value: true,
    };

    let result = interp.eval(&closure);
    match result {
        EvalResult::Value(Value::Closure { kind, captures, .. }) => {
            assert_eq!(kind, ClosureKind::FnOnce);
            assert_eq!(captures.len(), 1);
            assert_eq!(captures[0].0, "captured");
            assert_eq!(captures[0].1, Value::u32(42));
            assert_eq!(captures[0].2, Mutability::Shared);
        }
        other => panic!("expected closure value, got {:?}", other),
    }
}

#[test]
fn test_move_closure_without_captures_stays_fn() {
    let mut interp = Interpreter::new();

    let closure = Expr::Closure {
        params: vec![],
        body: Box::new(Expr::Literal(Value::u32(42))),
        captures: vec![],
        capture_by_value: true,
    };

    let result = interp.eval(&closure);
    match result {
        EvalResult::Value(Value::Closure { kind, captures, .. }) => {
            assert_eq!(kind, ClosureKind::Fn);
            assert!(captures.is_empty());
        }
        other => panic!("expected closure value, got {:?}", other),
    }
}

#[test]
fn test_move_closure_with_unresolved_capture_stays_fn() {
    let mut interp = Interpreter::new();

    let closure = Expr::Closure {
        params: vec![],
        body: Box::new(Expr::Literal(Value::u32(42))),
        captures: vec![("block_local".to_string(), Mutability::Shared)],
        capture_by_value: true,
    };

    let result = interp.eval(&closure);
    match result {
        EvalResult::Value(Value::Closure { kind, captures, .. }) => {
            assert_eq!(kind, ClosureKind::Fn);
            assert!(captures.is_empty());
        }
        other => panic!("expected closure value, got {:?}", other),
    }
}

fn make_capture_increment_closure(
    capture_name: &str,
    capture_mutability: Mutability,
    capture_by_value: bool,
) -> Expr {
    Expr::Closure {
        params: vec![],
        body: Box::new(Expr::Assign {
            target: Box::new(Expr::Var {
                name: capture_name.to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var {
                    name: capture_name.to_string(),
                    local_idx: 0,
                }),
                right: Box::new(Expr::Literal(Value::u32(1))),
            }),
        }),
        captures: vec![(capture_name.to_string(), capture_mutability)],
        capture_by_value,
    }
}

fn make_fnmut_increment_closure(capture_name: &str) -> Expr {
    make_capture_increment_closure(capture_name, Mutability::Mutable, false)
}

#[test]
fn test_fnmut_closure_mutation_propagates_across_calls() {
    let mut interp = Interpreter::new();
    interp.bind("x".to_string(), Value::u32(0));

    let closure_value = interp
        .eval(&make_fnmut_increment_closure("x"))
        .value()
        .expect("closure literal should evaluate to a closure");
    interp.bind("f".to_string(), closure_value);

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "f".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
    assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
    assert_eq!(interp.lookup("x"), Some(Value::u32(2)));
}

#[test]
fn test_fnmut_closure_writeback_targets_original_capture_place() {
    let mut interp = Interpreter::new();
    interp.bind("x".to_string(), Value::u32(0));

    let closure_value = interp
        .eval(&make_fnmut_increment_closure("x"))
        .value()
        .expect("closure literal should evaluate to a closure");
    interp.bind("f".to_string(), closure_value);

    interp.push_scope();
    interp.bind("x".to_string(), Value::u32(10));

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "f".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
    assert_eq!(
        interp.lookup("x"),
        Some(Value::u32(10)),
        "call-site shadow should remain untouched"
    );

    interp.pop_scope();
    assert_eq!(
        interp.lookup("x"),
        Some(Value::u32(1)),
        "writeback should update the original captured binding"
    );
}

#[test]
fn test_fnonce_closure_capture_mutation_does_not_write_back() {
    let mut interp = Interpreter::new();
    interp.bind("x".to_string(), Value::u32(0));

    let closure_value = interp
        .eval(&make_capture_increment_closure(
            "x",
            Mutability::Shared,
            true,
        ))
        .value()
        .expect("closure literal should evaluate to a closure");

    match &closure_value {
        Value::Closure { kind, .. } => assert_eq!(*kind, ClosureKind::FnOnce),
        other => panic!("expected closure value, got {other:?}"),
    }

    interp.bind("f".to_string(), closure_value);

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "f".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
    assert_eq!(
        interp.lookup("x"),
        Some(Value::u32(0)),
        "FnOnce captures are consumed by value and must not write back"
    );
}

#[test]
fn test_fn_closure_shared_capture_mutation_does_not_write_back() {
    let mut interp = Interpreter::new();
    interp.bind("x".to_string(), Value::u32(0));

    let closure_value = interp
        .eval(&make_capture_increment_closure(
            "x",
            Mutability::Shared,
            false,
        ))
        .value()
        .expect("closure literal should evaluate to a closure");

    match &closure_value {
        Value::Closure { kind, .. } => assert_eq!(*kind, ClosureKind::Fn),
        other => panic!("expected closure value, got {other:?}"),
    }

    interp.bind("f".to_string(), closure_value);

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "f".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
    assert_eq!(
        interp.lookup("x"),
        Some(Value::u32(0)),
        "shared captures stay local to Fn closure calls"
    );
}

#[test]
fn test_union_field_access_requires_unsafe() {
    let mut interp = Interpreter::new();

    // Create union value
    let union_val = Value::Union {
        name: "MyUnion".to_string(),
        active_field: "f1".to_string(),
        value: Box::new(Value::u32(42)),
    };

    // Reading union field outside unsafe should error
    let expr = Expr::UnionFieldAccess {
        union_expr: Box::new(Expr::Literal(union_val.clone())),
        field: "f1".to_string(),
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(e) => {
            assert!(e.contains("unsafe"), "error should mention unsafe: {}", e);
        }
        _ => panic!("expected error for union field access outside unsafe"),
    }
}

#[test]
fn test_union_field_access_in_unsafe() {
    let mut interp = Interpreter::new();

    // Create union value
    let union_val = Value::Union {
        name: "MyUnion".to_string(),
        active_field: "f1".to_string(),
        value: Box::new(Value::u32(42)),
    };

    // Reading same field in unsafe should succeed
    let expr = Expr::Unsafe {
        block: Box::new(Expr::UnionFieldAccess {
            union_expr: Box::new(Expr::Literal(union_val)),
            field: "f1".to_string(),
        }),
    };

    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_union_field_access_different_field() {
    let mut interp = Interpreter::new();

    // Create union with f1 as active field
    let union_val = Value::Union {
        name: "MyUnion".to_string(),
        active_field: "f1".to_string(),
        value: Box::new(Value::u32(42)),
    };

    // Reading different field (f2) should warn about potential UB
    let expr = Expr::Unsafe {
        block: Box::new(Expr::UnionFieldAccess {
            union_expr: Box::new(Expr::Literal(union_val)),
            field: "f2".to_string(),
        }),
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(e) => {
            assert!(
                e.contains("potential UB") || e.contains("last written"),
                "error should mention potential UB: {}",
                e
            );
        }
        _ => panic!("expected error for reading non-active union field"),
    }
}

// =========================================================================
// Panic semantics tests
// =========================================================================

#[test]
fn test_panic_basic() {
    let mut interp = Interpreter::new();

    // Simple panic with a literal message
    let expr = Expr::Panic {
        message: Box::new(Expr::Literal(Value::u32(42))),
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Panic(msg) => {
            assert!(
                msg.contains("42"),
                "panic message should contain value: {}",
                msg
            );
        }
        other => panic!("expected Panic result, got {:?}", other),
    }
}

#[test]
fn test_panic_propagates_through_block() {
    let mut interp = Interpreter::new();

    // Panic inside a block should propagate out
    let expr = Expr::Block {
        stmts: vec![
            Stmt::Expr(Expr::Literal(Value::u32(1))),
            Stmt::Expr(Expr::Panic {
                message: Box::new(Expr::Literal(Value::u32(999))),
            }),
            Stmt::Expr(Expr::Literal(Value::u32(2))), // Should not execute
        ],
        expr: Some(Box::new(Expr::Literal(Value::u32(3)))),
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Panic(msg) => {
            assert!(
                msg.contains("999"),
                "panic message should contain value: {}",
                msg
            );
        }
        other => panic!("expected Panic result, got {:?}", other),
    }
}

#[test]
fn test_panic_in_if_condition() {
    let mut interp = Interpreter::new();

    // Panic in if condition
    let expr = Expr::If {
        condition: Box::new(Expr::Panic {
            message: Box::new(Expr::Literal(Value::Bool(true))),
        }),
        then_branch: Box::new(Expr::Literal(Value::u32(1))),
        else_branch: Some(Box::new(Expr::Literal(Value::u32(2)))),
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Panic(_) => {}
        other => panic!("expected Panic result, got {:?}", other),
    }
}

#[test]
fn test_panic_vs_error() {
    // Panic and Error are different: Panic is explicit abort,
    // Error is evaluation failure
    let mut interp = Interpreter::new();

    // Panic - explicit program abort
    let panic_expr = Expr::Panic {
        message: Box::new(Expr::Literal(Value::u32(1))),
    };
    assert!(matches!(interp.eval(&panic_expr), EvalResult::Panic(_)));

    // Error - evaluation failure (e.g., field access on non-struct)
    let error_expr = Expr::Field {
        base: Box::new(Expr::Literal(Value::u32(42))),
        field: "x".to_string(),
    };
    assert!(matches!(interp.eval(&error_expr), EvalResult::Error(_)));
}

#[test]
fn test_panic_propagates_through_function_args() {
    let mut interp = Interpreter::new();

    // Panic in function argument should propagate before call executes
    // Use a closure that returns first arg to test arg evaluation
    // Closure: |x, y| x
    let closure = Expr::Closure {
        params: vec![
            ("x".to_string(), RustType::Int(IntType::I32)),
            ("y".to_string(), RustType::Int(IntType::I32)),
        ],
        body: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 1,
        }),
        captures: vec![],
        capture_by_value: false,
    };

    let expr = Expr::Call {
        func: Box::new(closure),
        args: vec![
            Expr::Literal(Value::i32(1)),
            Expr::Panic {
                message: Box::new(Expr::Literal(Value::i32(42))),
            },
        ],
        type_args: vec![],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Panic(msg) => {
            assert!(msg.contains("42"), "panic should propagate: {}", msg);
        }
        other => panic!("expected Panic from arg evaluation, got {:?}", other),
    }
}

#[test]
fn test_panic_in_match_arm() {
    let mut interp = Interpreter::new();

    // Panic inside a match arm body
    let expr = Expr::Match {
        scrutinee: Box::new(Expr::Literal(Value::u32(1))),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            guard: None,
            body: Expr::Panic {
                message: Box::new(Expr::Literal(Value::u32(777))),
            },
        }],
    };

    let result = interp.eval(&expr);
    match result {
        EvalResult::Panic(msg) => {
            assert!(
                msg.contains("777"),
                "panic should propagate from match arm: {}",
                msg
            );
        }
        other => panic!("expected Panic result, got {:?}", other),
    }
}

// =========================================================================
// let-else tests (#926)
// =========================================================================

#[test]
fn test_eval_let_else_match_succeeds() {
    // let Some(x) = Some(42) else { return 0 };
    // x  → should evaluate to 42
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::EnumVariant {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: crate::expr::EnumPatternPayload::Tuple(vec![Pattern::Binding {
                    name: "x".to_string(),
                    mutable: false,
                    subpattern: None,
                }]),
            },
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::Enum {
                name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Box::new(EnumPayload::Tuple(vec![Value::u32(42)])),
            }))),
            else_block: Some(Box::new(Expr::Return(Some(Box::new(Expr::Literal(
                Value::u32(0),
            )))))),
        }],
        expr: Some(Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::u32(42)),
        "let-else with matching pattern should bind x = 42"
    );
}

#[test]
fn test_eval_let_else_match_fails_diverges() {
    // let Some(x) = None else { return 99 };
    // x  → should not reach here; else block returns 99
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::EnumVariant {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: crate::expr::EnumPatternPayload::Tuple(vec![Pattern::Binding {
                    name: "x".to_string(),
                    mutable: false,
                    subpattern: None,
                }]),
            },
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::Enum {
                name: "Option".to_string(),
                variant: "None".to_string(),
                payload: Box::new(EnumPayload::Unit),
            }))),
            else_block: Some(Box::new(Expr::Return(Some(Box::new(Expr::Literal(
                Value::u32(99),
            )))))),
        }],
        expr: Some(Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    match result {
        EvalResult::Return(v) => assert_eq!(
            v,
            Value::u32(99),
            "let-else with non-matching pattern should return 99 from else block"
        ),
        other => panic!(
            "expected Return(99) from let-else divergence, got {:?}",
            other
        ),
    }
}

#[test]
fn test_eval_let_else_non_diverging_else_is_error() {
    // let Some(x) = None else { 42 };
    // The else block doesn't diverge — this is a semantic error
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::EnumVariant {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: crate::expr::EnumPatternPayload::Tuple(vec![Pattern::Binding {
                    name: "x".to_string(),
                    mutable: false,
                    subpattern: None,
                }]),
            },
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::Enum {
                name: "Option".to_string(),
                variant: "None".to_string(),
                payload: Box::new(EnumPayload::Unit),
            }))),
            else_block: Some(Box::new(Expr::Literal(Value::u32(42)))),
        }],
        expr: None,
    };
    let result = interp.eval(&block);
    match result {
        EvalResult::Error(msg) => assert!(
            msg.contains("must diverge"),
            "non-diverging else block should produce 'must diverge' error, got: {}",
            msg
        ),
        other => panic!(
            "expected Error for non-diverging else block, got {:?}",
            other
        ),
    }
}

#[test]
fn test_eval_let_else_with_tuple_pattern() {
    // let (a, 0) = (10, 0) else { return 0 };
    // a → should evaluate to 10
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Tuple(vec![
                Pattern::Binding {
                    name: "a".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                Pattern::Literal(Value::u32(0)),
            ]),
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::Tuple(vec![
                Value::u32(10),
                Value::u32(0),
            ])))),
            else_block: Some(Box::new(Expr::Return(Some(Box::new(Expr::Literal(
                Value::u32(0),
            )))))),
        }],
        expr: Some(Box::new(Expr::Var {
            name: "a".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(
        result.value(),
        Some(Value::u32(10)),
        "let-else with matching tuple pattern should bind a = 10"
    );
}

#[test]
fn test_eval_let_else_tuple_pattern_mismatch() {
    // let (a, 0) = (10, 1) else { return 77 };
    // Tuple literal doesn't match → else block diverges with return 77
    let mut interp = Interpreter::new();
    let block = Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Tuple(vec![
                Pattern::Binding {
                    name: "a".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                Pattern::Literal(Value::u32(0)),
            ]),
            ty: None,
            init: Some(Box::new(Expr::Literal(Value::Tuple(vec![
                Value::u32(10),
                Value::u32(1),
            ])))),
            else_block: Some(Box::new(Expr::Return(Some(Box::new(Expr::Literal(
                Value::u32(77),
            )))))),
        }],
        expr: Some(Box::new(Expr::Var {
            name: "a".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    match result {
        EvalResult::Return(v) => assert_eq!(
            v,
            Value::u32(77),
            "let-else with mismatched tuple should return 77"
        ),
        other => panic!(
            "expected Return(77) from let-else divergence, got {:?}",
            other
        ),
    }
}

// ---------------------------------------------------------------------------
// Stacked-borrows aliasing integration (eval-level)
// ---------------------------------------------------------------------------

#[test]
fn test_aliasing_checks_bind_and_read() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Bind directly into the base scope so pop_scope does not clean up
    // name_places before we can inspect the ownership state.
    interp.bind("x".to_string(), Value::u32(42));

    let result = interp.eval(&Expr::Var {
        name: "x".to_string(),
        local_idx: 0,
    });
    assert_eq!(result.value(), Some(Value::u32(42)));

    // Confirm ownership state recorded a root tag for the place.
    let place = interp.name_places.get("x").expect("x should have a Place");
    assert!(
        interp.ctx.ownership.root_tag(place).is_some(),
        "x should have a stacked-borrows root tag after bind"
    );
}

#[test]
fn test_aliasing_checks_mutable_assignment() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // let mut x = 1; x = 2; x
    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "x".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Literal(Value::u32(1)))),
                else_block: None,
            },
            Stmt::Expr(Expr::Assign {
                target: Box::new(Expr::Var {
                    name: "x".to_string(),
                    local_idx: 0,
                }),
                value: Box::new(Expr::Literal(Value::u32(2))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::u32(2)));
}

#[test]
fn test_aliasing_checks_disabled_by_default() {
    let interp = Interpreter::new();
    assert!(!interp.aliasing_checks);
    assert!(interp.name_places.is_empty());
}

#[test]
fn test_aliasing_checks_assign_place_field_succeeds() {
    // Verify that assign_place on a struct field succeeds when aliasing
    // checks are enabled and no conflicting borrows exist.
    //
    // Rust equivalent:
    //   let mut s = Point { x: 1, y: 2 };
    //   s.x = 10;
    //   s.x  // → 10
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    let block = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "s".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(Expr::Struct {
                    name: "Point".to_string(),
                    fields: vec![
                        ("x".to_string(), Expr::Literal(Value::u32(1))),
                        ("y".to_string(), Expr::Literal(Value::u32(2))),
                    ],
                    type_args: vec![],
                    const_args: vec![],
                })),
                else_block: None,
            },
            // s.x = 10
            Stmt::Expr(Expr::Assign {
                target: Box::new(Expr::Field {
                    base: Box::new(Expr::Var {
                        name: "s".to_string(),
                        local_idx: 0,
                    }),
                    field: "x".to_string(),
                }),
                value: Box::new(Expr::Literal(Value::u32(10))),
            }),
        ],
        expr: Some(Box::new(Expr::Field {
            base: Box::new(Expr::Var {
                name: "s".to_string(),
                local_idx: 0,
            }),
            field: "x".to_string(),
        })),
    };
    let result = interp.eval(&block);
    assert_eq!(result.value(), Some(Value::u32(10)));
}

#[test]
fn test_aliasing_checks_assign_place_invalidated_subplace_rejected() {
    // Verify that a stale stacked-borrows tag on a sub-place is
    // rejected when accessed.  Simulates the scenario where a reborrow
    // of `s.x` is invalidated by a root-tag write.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Bind `s = Point { x: 1, y: 2 }` directly in the base scope so
    // pop_scope does not remove the name_places entry.
    interp.bind(
        "s".to_string(),
        Value::Struct {
            name: "Point".to_string(),
            fields: [
                ("x".to_string(), Value::u32(1)),
                ("y".to_string(), Value::u32(2)),
            ]
            .into_iter()
            .collect(),
        },
    );

    // Get the root place for `s` and build the sub-place `s.x`.
    let root_place = interp.name_places.get("s").expect("s has a Place").clone();
    let sub_place = Place::Field {
        base: Box::new(root_place),
        field: "x".to_string(),
    };

    // Create a reborrow tag for `s.x` (simulates `&mut s.x`).
    let _reborrow_tag = interp
        .ctx
        .ownership
        .retag_place(&sub_place, BorrowPermission::Unique, None)
        .expect("retag should succeed");

    // Invalidate the reborrow by accessing `s.x` through the root tag.
    // In Stacked Borrows, a write through a lower tag pops everything above.
    let root_tag = interp
        .ctx
        .ownership
        .root_tag(&sub_place)
        .expect("sub_place should have a root from retag");
    interp
        .ctx
        .ownership
        .access_place(&sub_place, root_tag, AccessKind::Write)
        .expect("root write should succeed");

    // The reborrow tag is now popped from the borrow stack.
    // Verify that accessing through the dead reborrow tag fails.
    let access_result =
        interp
            .ctx
            .ownership
            .access_place(&sub_place, _reborrow_tag, AccessKind::Write);
    assert!(
        access_result.is_err(),
        "stale reborrow tag should be rejected by stacked borrows"
    );
}

// ---------------------------------------------------------------
// Function-call protector tests (Stacked Borrows #701)
// ---------------------------------------------------------------

/// Helper: register a function that dereferences its `&mut u32` param.
fn register_mut_ref_reader(interp: &mut Interpreter) {
    interp.ctx.register_function(FunctionDef {
        name: "read_ref".to_string(),
        params: vec![(
            "r".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Mutable,
                inner: Box::new(RustType::Uint(UintType::U32)),
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        })),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}

#[test]
fn test_call_function_creates_protector_for_mut_ref_param() {
    // Verify that calling a function with a real `&mut T` argument creates a
    // protector on the caller's referent. After the call returns,
    // the protector should be released.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    register_mut_ref_reader(&mut interp);

    // Bind directly in the base scope so the place survives for
    // post-call assertions.
    interp.bind("x".to_string(), Value::u32(10));

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "read_ref".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::AddrOf {
            mutability: Mutability::Mutable,
            expr: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            }),
        }],
        type_args: vec![],
    };

    let result = interp.eval(&call_expr);
    // The function should execute successfully and return 10.
    match result {
        EvalResult::Value(v) => assert_eq!(v, Value::u32(10)),
        other => panic!("expected Value(u32(10)), got {other:?}"),
    }

    // After the call, the protector should be released.  Verify by
    // checking that a root-tag write on x's place succeeds.
    let x_place = interp.place_for_name("x");
    let root = interp
        .ctx
        .ownership
        .root_tag(&x_place)
        .expect("x should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write)
        .expect("root write on x should succeed after call returns");
}

#[test]
fn test_bind_call_params_protects_caller_referent_during_mut_ref_call() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(10));

    let x_place = interp.place_for_name("x");
    let root = interp
        .ctx
        .ownership
        .root_tag(&x_place)
        .expect("x should have a root tag");
    let arg = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value @ Value::Reference { .. }) => value,
        other => panic!("expected &mut x to produce a reference, got {other:?}"),
    };

    interp.push_scope();
    interp.ctx.stack.push_frame();
    interp
        .bind_call_params(
            &[(
                "r".to_string(),
                RustType::Reference {
                    lifetime: Lifetime::Named("a".to_string()),
                    mutability: Mutability::Mutable,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
            )],
            vec![arg],
        )
        .expect("binding a protected call argument should succeed");

    let protected_tag = interp
        .ctx
        .ownership
        .borrow_stack(&x_place)
        .and_then(|stack| stack.last())
        .and_then(|entry| entry.protector.map(|_| entry.tag))
        .expect("call setup should leave a protected tag on the caller place");
    let err = interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write);
    assert!(matches!(
        err,
        Err(BorrowError::AliasingProtected { blocked_by, .. }) if blocked_by == protected_tag
    ));

    interp.release_current_frame_protectors();
    interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write)
        .expect("releasing call protectors should unblock the caller root write");
}

#[test]
fn test_addr_of_retags_place_under_aliasing_checks() {
    // When aliasing checks are on, `&mut x` should retag x's place,
    // creating a new derived borrow tag.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Bind `x = 5` directly in the interpreter's top scope so x stays live.
    interp.bind("x".to_string(), Value::u32(5));

    // Record the current borrow tag.
    let x_place = interp.place_for_name("x");
    let tag_before = interp
        .ctx
        .ownership
        .borrow_tag(&x_place)
        .expect("x should have a borrow tag after bind");

    // Evaluate `&mut x` to trigger a retag.
    let addr_of_expr = Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    };
    let result = interp.eval(&addr_of_expr);
    assert!(
        matches!(result, EvalResult::Value(Value::Reference { .. })),
        "addr_of should produce a reference, got: {result:?}"
    );

    // After retag, x's current tag should be different from the original.
    let tag_after = interp
        .ctx
        .ownership
        .borrow_tag(&x_place)
        .expect("x should still have a borrow tag");
    assert_ne!(
        tag_before, tag_after,
        "retag should produce a new derived borrow tag"
    );
}

#[test]
fn test_shared_addr_of_retags_with_readonly_permission() {
    // `&x` should create a SharedReadOnly retag, not a Unique one.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Bind `y = 7` directly so it stays in scope.
    interp.bind("y".to_string(), Value::u32(7));

    let y_place = interp.place_for_name("y");
    let tag_before = interp
        .ctx
        .ownership
        .borrow_tag(&y_place)
        .expect("y should have a tag");

    // `&y` — shared borrow
    let addr_of = Expr::AddrOf {
        mutability: Mutability::Shared,
        expr: Box::new(Expr::Var {
            name: "y".to_string(),
            local_idx: 0,
        }),
    };
    let result = interp.eval(&addr_of);
    assert!(matches!(result, EvalResult::Value(Value::Reference { .. })));

    let tag_after = interp
        .ctx
        .ownership
        .borrow_tag(&y_place)
        .expect("y should have a tag after shared retag");
    assert_ne!(tag_before, tag_after, "shared borrow should retag");

    // A read through the shared tag should succeed.
    interp
        .ctx
        .ownership
        .access_place(&y_place, tag_after, AccessKind::Read)
        .expect("read through shared borrow tag should work");
}

#[test]
fn test_call_function_multi_param_protectors_released() {
    // Verify that calling a function with TWO &mut params creates a
    // protector on each caller place and releases both after the call.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Register a function with two &mut params.
    interp.ctx.register_function(FunctionDef {
        name: "swap_mut".to_string(),
        params: vec![
            (
                "a".to_string(),
                RustType::Reference {
                    lifetime: Lifetime::Named("x".to_string()),
                    mutability: Mutability::Mutable,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
            ),
            (
                "b".to_string(),
                RustType::Reference {
                    lifetime: Lifetime::Named("y".to_string()),
                    mutability: Mutability::Mutable,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
            ),
        ],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Deref(Box::new(Expr::Var {
            name: "a".to_string(),
            local_idx: 0,
        })),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    // Bind x and y directly in the base scope so the places survive
    // for post-call assertions.
    interp.bind("x".to_string(), Value::u32(10));
    interp.bind("y".to_string(), Value::u32(20));

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "swap_mut".to_string(),
            local_idx: 0,
        }),
        args: vec![
            Expr::AddrOf {
                mutability: Mutability::Mutable,
                expr: Box::new(Expr::Var {
                    name: "x".to_string(),
                    local_idx: 0,
                }),
            },
            Expr::AddrOf {
                mutability: Mutability::Mutable,
                expr: Box::new(Expr::Var {
                    name: "y".to_string(),
                    local_idx: 0,
                }),
            },
        ],
        type_args: vec![],
    };

    let result = interp.eval(&call_expr);
    match result {
        EvalResult::Value(v) => assert_eq!(v, Value::u32(10)),
        other => panic!("expected Value(u32(10)), got {other:?}"),
    }

    // After the call both protectors should be released. Verify by
    // checking that root-tag writes on both places succeed.
    let x_place = interp.place_for_name("x");
    let root_x = interp
        .ctx
        .ownership
        .root_tag(&x_place)
        .expect("x should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&x_place, root_x, AccessKind::Write)
        .expect("root write on x should succeed after call returns");

    let y_place = interp.place_for_name("y");
    let root_y = interp
        .ctx
        .ownership
        .root_tag(&y_place)
        .expect("y should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&y_place, root_y, AccessKind::Write)
        .expect("root write on y should succeed after call returns");
}

/// Helper: register a function that dereferences its `&u32` (shared ref) param.
fn register_shared_ref_reader(interp: &mut Interpreter) {
    interp.ctx.register_function(FunctionDef {
        name: "read_shared".to_string(),
        params: vec![(
            "r".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Uint(UintType::U32)),
            },
        )],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        })),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}

#[test]
fn test_call_function_creates_protector_for_shared_ref_param() {
    // Verify that calling a function with a `&T` argument creates a
    // protector on the caller's referent, just like `&mut T`.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    register_shared_ref_reader(&mut interp);

    // Bind directly in the base scope so the place survives for
    // post-call assertions (Block pop_scope removes name_places).
    interp.bind("x".to_string(), Value::u32(42));

    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "read_shared".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::AddrOf {
            mutability: Mutability::Shared,
            expr: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            }),
        }],
        type_args: vec![],
    };

    let result = interp.eval(&call_expr);
    match result {
        EvalResult::Value(v) => assert_eq!(v, Value::u32(42)),
        other => panic!("expected Value(u32(42)), got {other:?}"),
    }

    // After the call, the protector should be released. Verify by
    // checking that a root-tag write on x's place succeeds.
    let x_place = interp.place_for_name("x");
    let root = interp
        .ctx
        .ownership
        .root_tag(&x_place)
        .expect("x should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write)
        .expect("root write on x should succeed after shared-ref call returns");
}

#[test]
fn test_bind_call_params_protects_caller_referent_during_shared_ref_call() {
    // Directly test that bind_call_params creates a protector for &T params.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(10));

    let x_place = interp.place_for_name("x");
    let root = interp
        .ctx
        .ownership
        .root_tag(&x_place)
        .expect("x should have a root tag");

    let arg = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Shared,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value @ Value::Reference { .. }) => value,
        other => panic!("expected &x to produce a reference, got {other:?}"),
    };

    interp.push_scope();
    interp.ctx.stack.push_frame();
    interp
        .bind_call_params(
            &[(
                "r".to_string(),
                RustType::Reference {
                    lifetime: Lifetime::Named("a".to_string()),
                    mutability: Mutability::Shared,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
            )],
            vec![arg],
        )
        .expect("binding a protected shared-ref call argument should succeed");

    // The protected shared borrow should block a root write.
    let protected_tag = interp
        .ctx
        .ownership
        .borrow_stack(&x_place)
        .and_then(|stack| stack.last())
        .and_then(|entry| entry.protector.map(|_| entry.tag))
        .expect("call setup should leave a protected tag on the caller place");
    let err = interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write);
    assert!(matches!(
        err,
        Err(BorrowError::AliasingProtected { blocked_by, .. }) if blocked_by == protected_tag
    ));

    interp.release_current_frame_protectors();
    interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write)
        .expect("releasing call protectors should unblock the caller root write");
}

#[test]
fn test_unique_retag_from_root_invalidates_derived_unique() {
    // Use the ownership API directly to demonstrate that a Unique retag
    // from the root parent invalidates a Unique entry above it, matching
    // Miri's retag semantics.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    interp.bind("x".to_string(), Value::u32(5));
    let x_place = interp.place_for_name("x");

    let root = interp
        .ctx
        .ownership
        .root_tag(&x_place)
        .expect("x should have a root tag");

    // Derive a Unique tag from root (simulates first &mut x).
    let first_unique = interp
        .ctx
        .ownership
        .retag_place(&x_place, BorrowPermission::Unique, None)
        .expect("first unique retag should succeed");

    // Derive a second Unique tag from root directly. This simulates
    // the reborrow pattern where the original owner reclaims exclusivity.
    // The first Unique entry should be invalidated because it is above root.
    let second_unique = interp
        .ctx
        .ownership
        .retag_place(&x_place, BorrowPermission::Unique, None)
        .expect("second unique retag should succeed");
    // retag_place chains from current tag (first_unique), so first_unique
    // is the parent and entries above it are empty. But we can verify
    // the derivation chain is properly formed.
    assert_ne!(first_unique, second_unique);

    // Verify: a write through the second Unique tag should invalidate
    // the first Unique tag via the access() popping semantics.
    interp
        .ctx
        .ownership
        .access_place(&x_place, root, AccessKind::Write)
        .expect("root write should succeed");

    let stack = interp
        .ctx
        .ownership
        .borrow_stack(&x_place)
        .expect("x should have a borrow stack");
    assert!(
        !stack.iter().any(|e| e.tag == first_unique),
        "first Unique tag should be invalidated by root write"
    );
    assert!(
        !stack.iter().any(|e| e.tag == second_unique),
        "second Unique tag should be invalidated by root write"
    );
}

// ---------------------------------------------------------------
// Expr::Deref borrow-stack validation (#701)
// ---------------------------------------------------------------

#[test]
fn test_deref_through_invalidated_tag_rejected() {
    // End-to-end: create `&mut x`, invalidate the tag, then `*r` must fail.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Bind `x = 42u32`.
    interp.bind("x".to_string(), Value::u32(42));

    // Create a mutable reference: `&mut x`
    let addr_of = Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    };
    let ref_val = match interp.eval(&addr_of) {
        EvalResult::Value(v) => v,
        other => panic!("expected reference, got {other:?}"),
    };

    // Bind the mutable reference to `r`.
    interp.bind("r".to_string(), ref_val.clone());

    // Find the referent place that `r` points to.
    let referent_place = interp
        .referenced_place(&ref_val)
        .expect("reference should have a tracked referent place");

    // Invalidate the borrow by writing through the root tag.
    let root = interp
        .ctx
        .ownership
        .root_tag(&referent_place)
        .expect("referent should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&referent_place, root, AccessKind::Write)
        .expect("root write should succeed and pop derived tags");

    // Dereference `*r` — should be rejected because the tag was popped.
    let deref_expr = Expr::Deref(Box::new(Expr::Var {
        name: "r".to_string(),
        local_idx: 0,
    }));
    let result = interp.eval(&deref_expr);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "deref through invalidated tag should be rejected, got {result:?}"
    );
}

#[test]
fn test_deref_with_live_tag_succeeds() {
    // Normal dereference through a live reference must succeed
    // even when aliasing checks are enabled.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    // Bind `x = 99u32` directly so it stays in scope.
    interp.bind("x".to_string(), Value::u32(99));

    // Create a shared reference: `&x`
    let addr_of = Expr::AddrOf {
        mutability: Mutability::Shared,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    };
    let ref_val = match interp.eval(&addr_of) {
        EvalResult::Value(v) => v,
        other => panic!("expected reference, got {other:?}"),
    };

    // Bind the reference to `r` directly.
    interp.bind("r".to_string(), ref_val);

    // Dereference `*r` — should succeed because the tag is live.
    let deref_expr = Expr::Deref(Box::new(Expr::Var {
        name: "r".to_string(),
        local_idx: 0,
    }));
    let result = interp.eval(&deref_expr);
    assert_eq!(
        result.value(),
        Some(Value::u32(99)),
        "deref through live shared reference should return the value"
    );
}

#[test]
fn test_raw_deref_through_invalidated_tag_rejected() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(7));

    let ref_val = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), ref_val.clone());

    let referent_place = interp
        .referenced_place(&ref_val)
        .expect("reference should track its referent place");
    let root = interp
        .ctx
        .ownership
        .root_tag(&referent_place)
        .expect("referent should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&referent_place, root, AccessKind::Write)
        .expect("root write should invalidate the derived reference tag");

    let raw_deref = Expr::Unsafe {
        block: Box::new(Expr::RawDeref(Box::new(Expr::Cast {
            expr: Box::new(Expr::Var {
                name: "r".to_string(),
                local_idx: 0,
            }),
            target: RustType::RawPtr {
                mutability: Mutability::Mutable,
                inner: Box::new(RustType::Uint(UintType::U32)),
            },
        }))),
    };
    let result = interp.eval(&raw_deref);
    // Some raw-deref error paths still wrap with the legacy "stacked borrows: …"
    // prefix while others use the new "borrow error [aliasing_*]" format.
    // Accept either since both indicate the invalidated-tag rejection.
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "raw deref through an invalidated tag should be rejected, got {result:?}"
    );
}

#[test]
fn test_raw_pointer_cast_from_invalidated_tag_rejected() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(7));

    let ref_val = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), ref_val.clone());

    let referent_place = interp
        .referenced_place(&ref_val)
        .expect("reference should track its referent place");
    let root = interp
        .ctx
        .ownership
        .root_tag(&referent_place)
        .expect("referent should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&referent_place, root, AccessKind::Write)
        .expect("root write should invalidate the derived reference tag");

    let cast = Expr::Cast {
        expr: Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }),
        target: RustType::RawPtr {
            mutability: Mutability::Mutable,
            inner: Box::new(RustType::Uint(UintType::U32)),
        },
    };
    let result = interp.eval(&cast);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("raw pointer cast rejected")),
        "casting an invalidated reference to a raw pointer should fail, got {result:?}"
    );
    assert!(
        interp.raw_pointer_places.is_empty(),
        "failed casts must not mint tracked raw-pointer provenance"
    );
}

#[test]
fn test_raw_deref_with_live_tag_reads_tracked_place() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(55));

    let ref_val = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Shared,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected shared reference, got {other:?}"),
    };
    interp.bind("r".to_string(), ref_val);

    let raw_deref = Expr::Unsafe {
        block: Box::new(Expr::RawDeref(Box::new(Expr::Cast {
            expr: Box::new(Expr::Var {
                name: "r".to_string(),
                local_idx: 0,
            }),
            target: RustType::RawPtr {
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Uint(UintType::U32)),
            },
        }))),
    };
    let result = interp.eval(&raw_deref);
    assert_eq!(
        result.value(),
        Some(Value::u32(55)),
        "raw deref should reuse tracked place provenance instead of reading zeroed backing memory"
    );
}

#[test]
fn test_mut_reborrow_from_raw_deref_reuses_tracked_place() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(1));

    let parent_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), parent_ref);

    let child_ref = match interp.eval(&Expr::Unsafe {
        block: Box::new(Expr::AddrOf {
            mutability: Mutability::Mutable,
            expr: Box::new(Expr::RawDeref(Box::new(Expr::Cast {
                expr: Box::new(Expr::Var {
                    name: "r".to_string(),
                    local_idx: 0,
                }),
                target: RustType::RawPtr {
                    mutability: Mutability::Mutable,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
            }))),
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable raw reborrow, got {other:?}"),
    };
    let x_place = interp.place_for_name("x");
    assert_eq!(
        interp.referenced_place(&child_ref),
        Some(x_place.clone()),
        "a mutable reborrow from raw deref should keep the original referent place"
    );
    interp.bind("s".to_string(), child_ref);

    let assign = Expr::Assign {
        target: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "s".to_string(),
            local_idx: 0,
        }))),
        value: Box::new(Expr::Literal(Value::u32(2))),
    };
    assert_eq!(interp.eval(&assign).value(), Some(Value::Unit));
    assert_eq!(
        interp
            .eval(&Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            })
            .value(),
        Some(Value::u32(2)),
        "writes through a raw-pointer reborrow should update the tracked referent"
    );
}

#[test]
fn test_parent_write_invalidates_shared_reborrow_from_raw_deref() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(1));

    let parent_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), parent_ref);

    let child_ref = match interp.eval(&Expr::Unsafe {
        block: Box::new(Expr::AddrOf {
            mutability: Mutability::Shared,
            expr: Box::new(Expr::RawDeref(Box::new(Expr::Cast {
                expr: Box::new(Expr::Var {
                    name: "r".to_string(),
                    local_idx: 0,
                }),
                target: RustType::RawPtr {
                    mutability: Mutability::Shared,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
            }))),
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected shared raw reborrow, got {other:?}"),
    };
    let x_place = interp.place_for_name("x");
    assert_eq!(
        interp.referenced_place(&child_ref),
        Some(x_place),
        "a shared reborrow from raw deref should keep the original referent place"
    );
    interp.bind("s".to_string(), child_ref);

    let parent_write = Expr::Assign {
        target: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }))),
        value: Box::new(Expr::Literal(Value::u32(2))),
    };
    assert_eq!(
        interp.eval(&parent_write).value(),
        Some(Value::Unit),
        "writing through the parent unique reference should succeed"
    );

    let child_read = interp.eval(&Expr::Deref(Box::new(Expr::Var {
        name: "s".to_string(),
        local_idx: 0,
    })));
    assert!(
        matches!(child_read, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "a parent write should invalidate the shared raw reborrow, got {child_read:?}"
    );
}

#[test]
fn test_assign_through_invalidated_deref_rejected() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(1));

    let ref_val = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), ref_val.clone());

    let referent_place = interp
        .referenced_place(&ref_val)
        .expect("reference should have a tracked referent place");
    let root = interp
        .ctx
        .ownership
        .root_tag(&referent_place)
        .expect("referent should have a root tag");
    interp
        .ctx
        .ownership
        .access_place(&referent_place, root, AccessKind::Write)
        .expect("root write should invalidate the derived mutable reference");

    let assign = Expr::Assign {
        target: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }))),
        value: Box::new(Expr::Literal(Value::u32(2))),
    };
    let result = interp.eval(&assign);
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "write through an invalidated deref should be rejected, got {result:?}"
    );
    assert_eq!(
        interp
            .eval(&Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            })
            .value(),
        Some(Value::u32(1)),
        "failed deref assignment must leave the referent unchanged"
    );
}

#[test]
fn test_assign_through_live_deref_updates_referent() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(1));

    let ref_val = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), ref_val);

    let assign = Expr::Assign {
        target: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }))),
        value: Box::new(Expr::Literal(Value::u32(2))),
    };
    let result = interp.eval(&assign);
    assert_eq!(result.value(), Some(Value::Unit));
    assert_eq!(
        interp
            .eval(&Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            })
            .value(),
        Some(Value::u32(2)),
        "deref assignment should update the tracked referent"
    );
    assert_eq!(
        interp
            .eval(&Expr::Deref(Box::new(Expr::Var {
                name: "r".to_string(),
                local_idx: 0,
            })))
            .value(),
        Some(Value::u32(2)),
        "subsequent deref reads should observe the updated referent"
    );
}

#[test]
fn test_mut_reborrow_reuses_tracked_referent_place() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(1));

    let parent_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), parent_ref);

    let child_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }))),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reborrow, got {other:?}"),
    };
    let x_place = interp.place_for_name("x");
    assert_eq!(
        interp.referenced_place(&child_ref),
        Some(x_place.clone()),
        "a mutable reborrow should keep the original referent place"
    );
    interp.bind("s".to_string(), child_ref);

    let assign = Expr::Assign {
        target: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "s".to_string(),
            local_idx: 0,
        }))),
        value: Box::new(Expr::Literal(Value::u32(2))),
    };
    assert_eq!(interp.eval(&assign).value(), Some(Value::Unit));
    assert_eq!(
        interp
            .eval(&Expr::Deref(Box::new(Expr::Var {
                name: "s".to_string(),
                local_idx: 0,
            })))
            .value(),
        Some(Value::u32(2)),
        "writes through a mutable reborrow should reach the tracked referent"
    );
}

#[test]
fn test_parent_access_invalidates_mut_reborrow() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("x".to_string(), Value::u32(1));

    let parent_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), parent_ref);

    let child_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }))),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reborrow, got {other:?}"),
    };
    interp.bind("s".to_string(), child_ref);

    assert_eq!(
        interp
            .eval(&Expr::Deref(Box::new(Expr::Var {
                name: "r".to_string(),
                local_idx: 0,
            })))
            .value(),
        Some(Value::u32(1)),
        "the parent reference should still be readable once"
    );

    let child_read = interp.eval(&Expr::Deref(Box::new(Expr::Var {
        name: "s".to_string(),
        local_idx: 0,
    })));
    assert!(
        matches!(child_read, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "reusing the parent should invalidate the child reborrow, got {child_read:?}"
    );
}

#[test]
fn test_addr_of_deref_operand_is_not_reexecuted_for_place_recovery() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    interp.bind("count".to_string(), Value::u32(0));
    interp.bind("x".to_string(), Value::u32(7));

    let parent_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };
    interp.bind("r".to_string(), parent_ref);

    let operand = Expr::Block {
        stmts: vec![Stmt::Expr(Expr::Assign {
            target: Box::new(Expr::Var {
                name: "count".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var {
                    name: "count".to_string(),
                    local_idx: 0,
                }),
                right: Box::new(Expr::Literal(Value::u32(1))),
            }),
        })],
        expr: Some(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        })),
    };

    let reborrow = interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Deref(Box::new(operand))),
    });
    assert!(
        matches!(reborrow, EvalResult::Value(Value::Reference { .. })),
        "taking `&mut *operand` should succeed, got {reborrow:?}"
    );
    assert_eq!(
        interp
            .eval(&Expr::Var {
                name: "count".to_string(),
                local_idx: 0,
            })
            .value(),
        Some(Value::u32(1)),
        "tracked-place recovery must not re-run the deref operand expression"
    );
}

#[test]
fn test_deref_after_same_scope_shadow_reads_original_binding() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    interp.bind("x".to_string(), Value::u32(11));
    let first_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Shared,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected shared reference, got {other:?}"),
    };

    interp.bind("x".to_string(), Value::u32(22));
    interp.bind("r".to_string(), first_ref);

    let result = interp.eval(&Expr::Deref(Box::new(Expr::Var {
        name: "r".to_string(),
        local_idx: 0,
    })));
    assert_eq!(
        result.value(),
        Some(Value::u32(11)),
        "same-scope shadowing must not retarget an existing reference to the newer binding"
    );
}

#[test]
fn test_assign_through_outer_reference_ignores_inner_shadow() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    interp.bind("x".to_string(), Value::u32(11));
    let outer_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Mutable,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected mutable reference, got {other:?}"),
    };

    interp.push_scope();
    interp.bind("x".to_string(), Value::u32(22));
    interp.bind("r".to_string(), outer_ref);

    let assign = Expr::Assign {
        target: Box::new(Expr::Deref(Box::new(Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        }))),
        value: Box::new(Expr::Literal(Value::u32(33))),
    };
    let assign_result = interp.eval(&assign);
    assert_eq!(
        assign_result.value(),
        Some(Value::Unit),
        "write through an outer reference should still succeed under inner shadowing"
    );
    assert_eq!(
        interp
            .eval(&Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            })
            .value(),
        Some(Value::u32(22)),
        "the visible inner shadow should remain unchanged"
    );
    assert_eq!(
        interp
            .eval(&Expr::Deref(Box::new(Expr::Var {
                name: "r".to_string(),
                local_idx: 0,
            })))
            .value(),
        Some(Value::u32(33)),
        "the outer binding should receive the write through its existing reference"
    );

    interp.pop_scope();
    assert_eq!(
        interp
            .eval(&Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            })
            .value(),
        Some(Value::u32(33)),
        "after the inner scope exits, the outer binding should expose the tracked update"
    );
}

#[test]
fn test_deref_after_scope_rebind_rejected() {
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;

    interp.push_scope();
    interp.bind("x".to_string(), Value::u32(11));
    let stale_ref = match interp.eval(&Expr::AddrOf {
        mutability: Mutability::Shared,
        expr: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
    }) {
        EvalResult::Value(value) => value,
        other => panic!("expected shared reference, got {other:?}"),
    };
    interp.pop_scope();

    interp.bind("x".to_string(), Value::u32(22));
    interp.bind("r".to_string(), stale_ref);

    let result = interp.eval(&Expr::Deref(Box::new(Expr::Var {
        name: "r".to_string(),
        local_idx: 0,
    })));
    assert!(
        matches!(
            result,
            EvalResult::Error(ref msg)
                if msg.contains("cannot resolve tracked place root")
                    || msg.contains("cannot read unbound tracked root")
        ),
        "deref through a stale tracked place must not attach to a later rebinding, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Generic monomorphization tests (#741)
// ---------------------------------------------------------------------------

/// `fn identity<T>(x: T) -> T { x }` called with explicit type arg `<u32>`.
#[test]
fn test_generic_function_identity_with_type_args() {
    let mut interp = Interpreter::new();

    // fn identity<T>(x: T) -> T { x }
    interp.ctx.register_function(FunctionDef {
        name: "identity".to_string(),
        params: vec![(
            "x".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
    });

    // identity::<u32>(42)
    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "identity".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(42))],
        type_args: vec![RustType::Uint(UintType::U32)],
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(42)));
}

/// Calling a generic function without type args still works (no substitution).
#[test]
fn test_generic_function_without_type_args() {
    let mut interp = Interpreter::new();

    // fn identity<T>(x: T) -> T { x }
    interp.ctx.register_function(FunctionDef {
        name: "identity".to_string(),
        params: vec![(
            "x".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
    });

    // identity(42) — no turbofish, still works
    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "identity".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(42))],
        type_args: vec![],
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(42)));
}

/// Type arity mismatch produces an error.
#[test]
fn test_generic_function_type_arg_arity_mismatch() {
    let mut interp = Interpreter::new();

    // fn identity<T>(x: T) -> T { x }
    interp.ctx.register_function(FunctionDef {
        name: "identity".to_string(),
        params: vec![(
            "x".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
    });

    // identity::<u32, bool>(42) — 2 type args for 1 type param
    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "identity".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(42))],
        type_args: vec![RustType::Uint(UintType::U32), RustType::Bool],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(&result, EvalResult::Error(msg) if msg.contains("type args")),
        "expected type arity mismatch error, got {result:?}"
    );
}

/// `fn first<A, B>(a: A, b: B) -> A { a }` with multiple type params.
#[test]
fn test_generic_function_multiple_type_params() {
    let mut interp = Interpreter::new();

    // fn first<A, B>(a: A, b: B) -> A { a }
    interp.ctx.register_function(FunctionDef {
        name: "first".to_string(),
        params: vec![
            (
                "a".to_string(),
                RustType::TypeParam(crate::types::TypeVar {
                    id: 0,
                    name: Some("A".to_string()),
                }),
            ),
            (
                "b".to_string(),
                RustType::TypeParam(crate::types::TypeVar {
                    id: 1,
                    name: Some("B".to_string()),
                }),
            ),
        ],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("A".to_string()),
        }),
        body: Expr::Var {
            name: "a".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![
            TypeParamDef {
                id: 0,
                name: "A".to_string(),
                bounds: vec![],
            },
            TypeParamDef {
                id: 1,
                name: "B".to_string(),
                bounds: vec![],
            },
        ],
    });

    // first::<u32, bool>(99, true) => 99
    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "first".to_string(),
            local_idx: 0,
        }),
        args: vec![
            Expr::Literal(Value::u32(99)),
            Expr::Literal(Value::Bool(true)),
        ],
        type_args: vec![RustType::Uint(UintType::U32), RustType::Bool],
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(99)));
}

#[test]
fn test_infer_call_type_param_subst_uses_declared_ids() {
    let interp = Interpreter::new();
    let params = vec![(
        "value".to_string(),
        RustType::TypeParam(crate::types::TypeVar {
            id: 7,
            name: Some("T".to_string()),
        }),
    )];
    let args = vec![Value::u32(42)];

    let subst = interp.infer_call_type_param_subst(&params, &args);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[&7], RustType::Uint(UintType::U32));
}

#[test]
fn test_infer_call_type_param_subst_accepts_mut_ref_for_shared_ref_param() {
    let interp = Interpreter::new();
    let params = vec![(
        "value".to_string(),
        RustType::Reference {
            lifetime: Lifetime::Anonymous(0),
            mutability: Mutability::Shared,
            inner: Box::new(RustType::TypeParam(crate::types::TypeVar {
                id: 5,
                name: Some("T".to_string()),
            })),
        },
    )];
    let args = vec![Value::Reference {
        addr: Address::new(AllocId(1), 0),
        mutability: Mutability::Mutable,
        lifetime: Lifetime::Anonymous(1),
        referent: Some(Box::new(Value::u32(7))),
    }];

    let subst = interp.infer_call_type_param_subst(&params, &args);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[&5], RustType::Uint(UintType::U32));
}

#[test]
fn test_generic_method_identity_with_type_args() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "keep".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Wrapper".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            (
                "value".to_string(),
                RustType::TypeParam(crate::types::TypeVar {
                    id: 7,
                    name: Some("T".to_string()),
                }),
            ),
        ],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 7,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "value".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 7,
            name: "T".to_string(),
            bounds: vec![],
        }],
    });

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Struct {
            name: "Wrapper".to_string(),
            fields: BTreeMap::new(),
        })),
        method: "keep".to_string(),
        args: vec![Expr::Literal(Value::u32(42))],
        type_args: vec![RustType::Uint(UintType::U32)],
    };

    assert_eq!(interp.eval(&expr).value(), Some(Value::u32(42)));
}

#[test]
fn test_generic_method_type_arg_arity_mismatch() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "keep".to_string(),
        params: vec![
            (
                "self".to_string(),
                RustType::Named {
                    name: "Wrapper".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
            (
                "value".to_string(),
                RustType::TypeParam(crate::types::TypeVar {
                    id: 7,
                    name: Some("T".to_string()),
                }),
            ),
        ],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 7,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "value".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 7,
            name: "T".to_string(),
            bounds: vec![],
        }],
    });

    let expr = Expr::MethodCall {
        receiver: Box::new(Expr::Literal(Value::Struct {
            name: "Wrapper".to_string(),
            fields: BTreeMap::new(),
        })),
        method: "keep".to_string(),
        args: vec![Expr::Literal(Value::u32(42))],
        type_args: vec![RustType::Uint(UintType::U32), RustType::Bool],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(&result, EvalResult::Error(msg) if msg.contains("type args")),
        "expected type arity mismatch error, got {result:?}"
    );
}

#[test]
fn test_generic_function_trait_bound_rejected_without_impl() {
    let mut interp = Interpreter::new();
    interp.ctx.register_trait_def("Marker".to_string(), vec![]);
    interp.ctx.register_function(FunctionDef {
        name: "keep".to_string(),
        params: vec![(
            "value".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "value".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec!["Marker".to_string()],
        }],
    });

    let result = interp.eval(&Expr::Call {
        func: Box::new(Expr::Var {
            name: "keep".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::Struct {
            name: "Bad".to_string(),
            fields: BTreeMap::new(),
        })],
        type_args: vec![],
    });

    assert!(
        matches!(&result, EvalResult::Error(msg) if msg.contains("Marker") && msg.contains("T")),
        "expected trait-bound error, got {result:?}"
    );
}

#[test]
fn test_impl_context_generic_bound_rejected_without_impl() {
    let mut interp = Interpreter::new();
    interp.ctx.register_trait_def("Marker".to_string(), vec![]);
    interp.ctx.register_function(FunctionDef {
        name: "Wrapper::take".to_string(),
        params: vec![(
            "value".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "value".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp.ctx.register_function_context_type_params(
        "Wrapper::take".to_string(),
        vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec!["Marker".to_string()],
        }],
    );

    let result = interp.eval(&Expr::Call {
        func: Box::new(Expr::Var {
            name: "Wrapper::take".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::Struct {
            name: "Bad".to_string(),
            fields: BTreeMap::new(),
        })],
        type_args: vec![],
    });

    assert!(
        matches!(&result, EvalResult::Error(msg) if msg.contains("Marker") && msg.contains("T")),
        "expected impl-context trait-bound error, got {result:?}"
    );
}

#[test]
fn test_impl_context_generic_bound_satisfied_with_registered_impl() {
    let mut interp = Interpreter::new();
    interp.ctx.register_trait_def("Marker".to_string(), vec![]);
    interp.ctx.register_trait_impl(
        "Marker".to_string(),
        RustType::Named {
            name: "Good".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        },
    );
    interp.ctx.register_function(FunctionDef {
        name: "Wrapper::take".to_string(),
        params: vec![(
            "value".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        ret_ty: RustType::TypeParam(crate::types::TypeVar {
            id: 0,
            name: Some("T".to_string()),
        }),
        body: Expr::Var {
            name: "value".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp.ctx.register_function_context_type_params(
        "Wrapper::take".to_string(),
        vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec!["Marker".to_string()],
        }],
    );

    let result = interp.eval(&Expr::Call {
        func: Box::new(Expr::Var {
            name: "Wrapper::take".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::Struct {
            name: "Good".to_string(),
            fields: BTreeMap::new(),
        })],
        type_args: vec![],
    });

    assert_eq!(
        result.value(),
        Some(Value::Struct {
            name: "Good".to_string(),
            fields: BTreeMap::new(),
        })
    );
}

#[test]
fn test_generic_struct_with_type_args() {
    use crate::types::TypeParamDef;

    let mut interp = Interpreter::new();

    // Register generic struct: struct Wrapper<T> { value: T }
    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Wrapper".to_string(),
        fields: vec![(
            "value".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });

    // Construct Wrapper::<i32> { value: 42 }
    let expr = Expr::Struct {
        name: "Wrapper".to_string(),
        fields: vec![("value".to_string(), Expr::Literal(Value::i32(42)))],
        type_args: vec![RustType::Int(IntType::I32)],
        const_args: vec![],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Struct {
            name: "Wrapper".to_string(),
            fields: {
                let mut m = BTreeMap::new();
                m.insert("value".to_string(), Value::i32(42));
                m
            },
        })
    );
}

#[test]
fn test_generic_struct_without_type_args_uses_raw_fields() {
    use crate::types::TypeParamDef;

    let mut interp = Interpreter::new();

    // Register generic struct without providing type args at construction
    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Wrapper".to_string(),
        fields: vec![(
            "value".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });

    // Construct Wrapper { value: 42 } — no explicit type args
    let expr = Expr::Struct {
        name: "Wrapper".to_string(),
        fields: vec![("value".to_string(), Expr::Literal(Value::i32(42)))],
        type_args: vec![],
        const_args: vec![],
    };

    // Should still succeed — no substitution, value used as-is
    let result = interp.eval(&expr);
    assert!(result.value().is_some());
}

#[test]
fn test_generic_struct_with_const_args() {
    let mut interp = Interpreter::new();

    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Buffer".to_string(),
        fields: vec![(
            "data".to_string(),
            RustType::Array {
                element: Box::new(RustType::Uint(UintType::U8)),
                len: ConstGenericArg::Param("N".to_string()),
            },
        )],
        type_params: vec![],
        const_params: vec![ConstParamDef {
            name: "N".to_string(),
            ty: RustType::Uint(UintType::Usize),
        }],
    });

    let expr = Expr::Struct {
        name: "Buffer".to_string(),
        fields: vec![(
            "data".to_string(),
            Expr::Array(vec![
                Expr::Literal(Value::u8(1)),
                Expr::Literal(Value::u8(2)),
                Expr::Literal(Value::u8(3)),
                Expr::Literal(Value::u8(4)),
            ]),
        )],
        type_args: vec![],
        const_args: vec![ConstGenericArg::usize(4)],
    };

    let result = interp.eval(&expr);
    assert_eq!(
        result.value(),
        Some(Value::Struct {
            name: "Buffer".to_string(),
            fields: {
                let mut m = BTreeMap::new();
                m.insert(
                    "data".to_string(),
                    Value::Array(vec![Value::u8(1), Value::u8(2), Value::u8(3), Value::u8(4)]),
                );
                m
            },
        })
    );
}

#[test]
fn test_generic_struct_type_arg_arity_mismatch() {
    use crate::types::TypeParamDef;

    let mut interp = Interpreter::new();

    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Wrapper".to_string(),
        fields: vec![(
            "value".to_string(),
            RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            }),
        )],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });

    let expr = Expr::Struct {
        name: "Wrapper".to_string(),
        fields: vec![("value".to_string(), Expr::Literal(Value::i32(42)))],
        type_args: vec![RustType::Int(IntType::I32), RustType::Bool],
        const_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(&result, EvalResult::Error(msg) if msg.contains("Wrapper") && msg.contains("type args")),
        "expected type arity mismatch error, got {result:?}"
    );
}

#[test]
fn test_generic_enum_tuple_variant_with_type_args() {
    use crate::stmt::{EnumVariantDef, EnumVariantType};
    use crate::types::TypeParamDef;

    let mut interp = Interpreter::new();

    // Register enum MyOption<T> { Some(T), None }
    interp.ctx.register_type(crate::stmt::TypeDef::Enum {
        name: "MyOption".to_string(),
        variants: vec![
            EnumVariantDef {
                name: "Some".to_string(),
                payload: EnumVariantType::Tuple(vec![RustType::TypeParam(crate::types::TypeVar {
                    id: 0,
                    name: Some("T".to_string()),
                })]),
                discriminant: None,
            },
            EnumVariantDef {
                name: "None".to_string(),
                payload: EnumVariantType::Unit,
                discriminant: None,
            },
        ],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });

    // Construct MyOption::<i32>::Some(42)
    let expr = Expr::EnumVariant {
        enum_name: "MyOption".to_string(),
        variant: "Some".to_string(),
        payload: EnumVariantPayload::Tuple(vec![Expr::Literal(Value::i32(42))]),
        type_args: vec![RustType::Int(IntType::I32)],
        const_args: vec![],
    };

    let result = interp.eval(&expr);
    match result.value() {
        Some(Value::Enum { name, variant, .. }) => {
            assert_eq!(name, "MyOption");
            assert_eq!(variant, "Some");
        }
        other => panic!("expected Enum, got {other:?}"),
    }
}

#[test]
fn test_generic_enum_without_type_args() {
    use crate::stmt::{EnumVariantDef, EnumVariantType};
    use crate::types::TypeParamDef;

    let mut interp = Interpreter::new();

    interp.ctx.register_type(crate::stmt::TypeDef::Enum {
        name: "MyOption".to_string(),
        variants: vec![EnumVariantDef {
            name: "Some".to_string(),
            payload: EnumVariantType::Tuple(vec![RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            })]),
            discriminant: None,
        }],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });

    // Construct MyOption::Some(42) without explicit type_args
    let expr = Expr::EnumVariant {
        enum_name: "MyOption".to_string(),
        variant: "Some".to_string(),
        payload: EnumVariantPayload::Tuple(vec![Expr::Literal(Value::i32(42))]),
        type_args: vec![],
        const_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(result.value().is_some());
}

#[test]
fn test_generic_enum_type_arg_arity_mismatch() {
    use crate::stmt::{EnumVariantDef, EnumVariantType};
    use crate::types::TypeParamDef;

    let mut interp = Interpreter::new();

    interp.ctx.register_type(crate::stmt::TypeDef::Enum {
        name: "MyOption".to_string(),
        variants: vec![EnumVariantDef {
            name: "Some".to_string(),
            payload: EnumVariantType::Tuple(vec![RustType::TypeParam(crate::types::TypeVar {
                id: 0,
                name: Some("T".to_string()),
            })]),
            discriminant: None,
        }],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });

    let expr = Expr::EnumVariant {
        enum_name: "MyOption".to_string(),
        variant: "Some".to_string(),
        payload: EnumVariantPayload::Tuple(vec![Expr::Literal(Value::i32(42))]),
        type_args: vec![RustType::Int(IntType::I32), RustType::Bool],
        const_args: vec![],
    };

    let result = interp.eval(&expr);
    assert!(
        matches!(&result, EvalResult::Error(msg) if msg.contains("MyOption") && msg.contains("type args")),
        "expected type arity mismatch error, got {result:?}"
    );
}

// ── async / await ──────────────────────────────────────────────────

#[test]
fn test_async_block_produces_future() {
    let mut interp = Interpreter::new();
    let expr = Expr::Async {
        capture_by_value: false,
        body: Box::new(Expr::Literal(Value::u32(42))),
    };
    let result = interp.eval(&expr);
    assert!(matches!(result.value(), Some(Value::Future { .. })));
}

#[test]
fn test_await_evaluates_future_synchronously() {
    let mut interp = Interpreter::new();
    // async { 42 }.await  →  42
    let expr = Expr::Await {
        base: Box::new(Expr::Async {
            capture_by_value: false,
            body: Box::new(Expr::Literal(Value::u32(42))),
        }),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_await_on_non_future_is_error() {
    let mut interp = Interpreter::new();
    let expr = Expr::Await {
        base: Box::new(Expr::Literal(Value::u32(99))),
    };
    let result = interp.eval(&expr);
    match result {
        EvalResult::Error(msg) => assert!(
            msg.contains("non-future"),
            "expected non-future error, got: {msg}"
        ),
        other => panic!("expected Error for await on non-future, got {:?}", other),
    }
}

#[test]
fn test_async_fn_returns_future() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "fetch".to_string(),
        params: vec![("x".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: true,
        type_params: vec![],
    });

    let expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "fetch".to_string(),
            local_idx: 0,
        }),
        args: vec![Expr::Literal(Value::u32(7))],
        type_args: vec![],
    };
    let result = interp.eval(&expr);
    assert!(matches!(result.value(), Some(Value::Future { .. })));
}

#[test]
fn test_async_fn_await_produces_value() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "fetch".to_string(),
        params: vec![("x".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        is_unsafe: false,
        is_async: true,
        type_params: vec![],
    });

    // fetch(7).await  →  7
    let expr = Expr::Await {
        base: Box::new(Expr::Call {
            func: Box::new(Expr::Var {
                name: "fetch".to_string(),
                local_idx: 0,
            }),
            args: vec![Expr::Literal(Value::u32(7))],
            type_args: vec![],
        }),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_async_fn_captures_args_by_value() {
    let mut interp = Interpreter::new();
    interp.ctx.register_function(FunctionDef {
        name: "double".to_string(),
        params: vec![("n".to_string(), RustType::Uint(UintType::U32))],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Var {
                name: "n".to_string(),
                local_idx: 0,
            }),
            right: Box::new(Expr::Var {
                name: "n".to_string(),
                local_idx: 0,
            }),
        },
        is_unsafe: false,
        is_async: true,
        type_params: vec![],
    });

    let expr = Expr::Await {
        base: Box::new(Expr::Call {
            func: Box::new(Expr::Var {
                name: "double".to_string(),
                local_idx: 0,
            }),
            args: vec![Expr::Literal(Value::u32(5))],
            type_args: vec![],
        }),
    };
    let result = interp.eval(&expr);
    assert_eq!(result.value(), Some(Value::u32(10)));
}

#[test]
fn test_async_block_move_capture() {
    let mut interp = Interpreter::new();
    let expr = Expr::Async {
        capture_by_value: true,
        body: Box::new(Expr::Literal(Value::Bool(true))),
    };
    let result = interp.eval(&expr);
    assert!(matches!(result.value(), Some(Value::Future { .. })));
}

// ---------------------------------------------------------------------------
// Drop implementation tests (#3047)
// ---------------------------------------------------------------------------

use super::tests_support::{make_let, make_mut_ref_named_type, make_named_type};

#[test]
fn test_call_drop_invokes_drop_impl() {
    use std::collections::BTreeMap;

    let mut interp = Interpreter::new();

    // Register a drop function that reads a field through `&mut self`.
    interp.ctx.register_function(FunctionDef {
        name: "MyType_drop".to_string(),
        params: vec![("_self".to_string(), make_mut_ref_named_type("MyType"))],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: "_dropped".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Field {
                base: Box::new(Expr::Deref(Box::new(Expr::Var {
                    name: "_self".to_string(),
                    local_idx: 0,
                }))),
                field: "armed".to_string(),
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl("MyType".to_string(), "MyType_drop".to_string());

    let mut my_type_fields = BTreeMap::new();
    my_type_fields.insert("armed".to_string(), Value::Bool(true));

    // _dropped = false; { let x = MyType{}; } // x dropped here; _dropped
    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "x",
                    false,
                    Some(make_named_type("MyType")),
                    Expr::Literal(Value::Struct {
                        name: "MyType".to_string(),
                        fields: my_type_fields,
                    }),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "Drop impl should receive a live &mut self when MyType goes out of scope"
    );
}

#[test]
fn test_call_drop_does_not_fallback_to_by_value_receiver() {
    use std::collections::BTreeMap;

    let mut interp = Interpreter::new();

    interp.ctx.register_function(FunctionDef {
        name: "MyType_drop".to_string(),
        params: vec![("_self".to_string(), make_named_type("MyType"))],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: "_dropped".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Literal(Value::Bool(true))),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl("MyType".to_string(), "MyType_drop".to_string());

    let mut my_type_fields = BTreeMap::new();
    my_type_fields.insert("armed".to_string(), Value::Bool(true));

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "x",
                    false,
                    Some(make_named_type("MyType")),
                    Expr::Literal(Value::Struct {
                        name: "MyType".to_string(),
                        fields: my_type_fields,
                    }),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(false)),
        "call_drop must not silently reuse the old by-value receiver path"
    );
}

#[test]
fn test_call_drop_recursive_named_struct_fields() {
    use std::collections::BTreeMap;

    let mut interp = Interpreter::new();

    // Register drop for Inner type using the real `&mut self` contract.
    interp.ctx.register_function(FunctionDef {
        name: "Inner_drop".to_string(),
        params: vec![("_self".to_string(), make_mut_ref_named_type("Inner"))],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: "_inner_dropped".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Field {
                base: Box::new(Expr::Deref(Box::new(Expr::Var {
                    name: "_self".to_string(),
                    local_idx: 0,
                }))),
                field: "armed".to_string(),
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl("Inner".to_string(), "Inner_drop".to_string());

    let mut inner_fields = BTreeMap::new();
    inner_fields.insert("armed".to_string(), Value::Bool(true));

    // Outer struct contains an Inner field — dropping Outer should drop Inner too
    let mut outer_fields = BTreeMap::new();
    outer_fields.insert(
        "inner".to_string(),
        Value::Struct {
            name: "Inner".to_string(),
            fields: inner_fields,
        },
    );

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_inner_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "outer",
                    false,
                    Some(make_named_type("Outer")),
                    Expr::Literal(Value::Struct {
                        name: "Outer".to_string(),
                        fields: outer_fields,
                    }),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_inner_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "Named-field drop should call Inner::drop with a live &mut self receiver"
    );
}

#[test]
fn test_call_drop_recursive_named_array_elements() {
    use std::collections::BTreeMap;

    let mut interp = Interpreter::new();

    interp.ctx.register_function(FunctionDef {
        name: "Inner_drop".to_string(),
        params: vec![("_self".to_string(), make_mut_ref_named_type("Inner"))],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: "_inner_dropped".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Field {
                base: Box::new(Expr::Deref(Box::new(Expr::Var {
                    name: "_self".to_string(),
                    local_idx: 0,
                }))),
                field: "armed".to_string(),
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp
        .ctx
        .register_drop_impl("Inner".to_string(), "Inner_drop".to_string());

    let mut inner_fields = BTreeMap::new();
    inner_fields.insert("armed".to_string(), Value::Bool(true));

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_inner_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "inners",
                    false,
                    Some(RustType::Array {
                        element: Box::new(make_named_type("Inner")),
                        len: ConstGenericArg::usize(1),
                    }),
                    Expr::Array(vec![Expr::Literal(Value::Struct {
                        name: "Inner".to_string(),
                        fields: inner_fields,
                    })]),
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_inner_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::Bool(true)),
        "Array-element drop should call Inner::drop with a live &mut self receiver via Place::Index"
    );
}

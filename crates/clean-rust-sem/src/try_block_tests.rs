// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::values::Value;

// ----------------------------------------------------------------
// TryBlock construction
// ----------------------------------------------------------------

#[test]
fn test_try_block_result_wraps_body_in_ok() {
    let tb = TryBlock {
        body: Expr::Literal(Value::u32(42)),
        result_type: TryResultType::Result,
    };
    let desugared = desugar_try_block(&tb);

    // Should be Loop { label, body: Break { label, value: Ok(42) } }
    match &desugared {
        Expr::Loop {
            label: Some(lbl),
            body,
        } => {
            assert!(lbl.starts_with("__try_"));
            match body.as_ref() {
                Expr::Break {
                    label: Some(brk_lbl),
                    value: Some(val),
                } => {
                    assert_eq!(lbl, brk_lbl);
                    match val.as_ref() {
                        Expr::EnumVariant {
                            enum_name,
                            variant,
                            payload: EnumVariantPayload::Tuple(args),
                            ..
                        } => {
                            assert_eq!(enum_name, "Result");
                            assert_eq!(variant, "Ok");
                            assert_eq!(args.len(), 1);
                            assert!(matches!(&args[0], Expr::Literal(Value::Uint { .. })));
                        }
                        other => panic!("expected EnumVariant Ok, got {other:?}"),
                    }
                }
                other => panic!("expected Break, got {other:?}"),
            }
        }
        other => panic!("expected Loop, got {other:?}"),
    }
}

#[test]
fn test_try_block_option_wraps_body_in_some() {
    let tb = TryBlock {
        body: Expr::Literal(Value::Bool(true)),
        result_type: TryResultType::Option,
    };
    let desugared = desugar_try_block(&tb);

    match &desugared {
        Expr::Loop { body, .. } => match body.as_ref() {
            Expr::Break {
                value: Some(val), ..
            } => match val.as_ref() {
                Expr::EnumVariant {
                    enum_name, variant, ..
                } => {
                    assert_eq!(enum_name, "Option");
                    assert_eq!(variant, "Some");
                }
                other => panic!("expected Some variant, got {other:?}"),
            },
            other => panic!("expected Break, got {other:?}"),
        },
        other => panic!("expected Loop, got {other:?}"),
    }
}

// ----------------------------------------------------------------
// QuestionMarkOp desugaring
// ----------------------------------------------------------------

#[test]
fn test_question_mark_function_level_uses_return() {
    let qm = QuestionMarkOp {
        expr: Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        },
        try_label: None,
    };
    let desugared = desugar_question_mark(&qm);

    // The Err arm should use Return
    match &desugared {
        Expr::Match { arms, .. } => {
            assert_eq!(arms.len(), 4);
            // arms[1] = Result::Err => return Err(e)
            assert!(matches!(&arms[1].body, Expr::Return(Some(_))));
            // arms[3] = Option::None => return None
            assert!(matches!(&arms[3].body, Expr::Return(Some(_))));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_question_mark_try_level_uses_break() {
    let label = "__try_test".to_string();
    let qm = QuestionMarkOp {
        expr: Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        },
        try_label: Some(label.clone()),
    };
    let desugared = desugar_question_mark(&qm);

    match &desugared {
        Expr::Match { arms, .. } => {
            assert_eq!(arms.len(), 4);
            // arms[1] = Result::Err => break 'label Err(e)
            match &arms[1].body {
                Expr::Break {
                    label: Some(lbl),
                    value: Some(val),
                } => {
                    assert_eq!(lbl, &label);
                    assert!(is_result_err(val));
                }
                other => panic!("expected Break with Err, got {other:?}"),
            }
            // arms[3] = Option::None => break 'label None
            match &arms[3].body {
                Expr::Break {
                    label: Some(lbl),
                    value: Some(val),
                } => {
                    assert_eq!(lbl, &label);
                    assert!(is_option_none(val));
                }
                other => panic!("expected Break with None, got {other:?}"),
            }
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_question_mark_ok_arm_extracts_value() {
    let qm = QuestionMarkOp {
        expr: Expr::Literal(Value::Unit),
        try_label: None,
    };
    let desugared = desugar_question_mark(&qm);

    match &desugared {
        Expr::Match { arms, .. } => {
            // arms[0] = Result::Ok(val) => val
            match &arms[0].pattern {
                Pattern::EnumVariant {
                    enum_name,
                    variant,
                    payload: EnumPatternPayload::Tuple(pats),
                } => {
                    assert_eq!(enum_name, "Result");
                    assert_eq!(variant, "Ok");
                    assert_eq!(pats.len(), 1);
                }
                other => panic!("expected Ok pattern, got {other:?}"),
            }
            // Body should be a variable reference
            assert!(matches!(&arms[0].body, Expr::Var { .. }));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

// ----------------------------------------------------------------
// Nested try blocks
// ----------------------------------------------------------------

#[test]
fn test_nested_try_blocks_get_distinct_labels() {
    let inner = TryBlock {
        body: Expr::Literal(Value::u32(1)),
        result_type: TryResultType::Result,
    };
    let inner_desugared = desugar_try_block(&inner);

    let outer = TryBlock {
        body: inner_desugared,
        result_type: TryResultType::Result,
    };
    let outer_desugared = desugar_try_block(&outer);

    // Extract labels from nested loops
    let outer_label = match &outer_desugared {
        Expr::Loop {
            label: Some(lbl), ..
        } => lbl.clone(),
        other => panic!("expected outer Loop, got {other:?}"),
    };

    // The inner loop is inside the break value (Ok(inner_loop))
    let inner_label = match &outer_desugared {
        Expr::Loop { body, .. } => match body.as_ref() {
            Expr::Break {
                value: Some(val), ..
            } => match val.as_ref() {
                Expr::EnumVariant {
                    payload: EnumVariantPayload::Tuple(args),
                    ..
                } => match &args[0] {
                    Expr::Loop {
                        label: Some(lbl), ..
                    } => lbl.clone(),
                    other => panic!("expected inner Loop, got {other:?}"),
                },
                other => panic!("expected EnumVariant, got {other:?}"),
            },
            other => panic!("expected Break, got {other:?}"),
        },
        other => panic!("expected Loop, got {other:?}"),
    };

    assert_ne!(
        outer_label, inner_label,
        "nested try blocks must have distinct labels"
    );
}

// ----------------------------------------------------------------
// Return rewriting in try context
// ----------------------------------------------------------------

#[test]
fn test_try_block_rewrites_return_err_to_break() {
    // Simulate: try { return Err(99) }
    // The return Err should become break 'label Err(99)
    let tb = TryBlock {
        body: Expr::Return(Some(Box::new(wrap_in_result_err(Expr::Literal(
            Value::u32(99),
        ))))),
        result_type: TryResultType::Result,
    };
    let desugared = desugar_try_block(&tb);

    // The body inside Ok(...) should now be Break instead of Return
    let label = match &desugared {
        Expr::Loop {
            label: Some(lbl), ..
        } => lbl.clone(),
        other => panic!("expected Loop, got {other:?}"),
    };

    match &desugared {
        Expr::Loop { body, .. } => match body.as_ref() {
            Expr::Break {
                value: Some(val), ..
            } => match val.as_ref() {
                Expr::EnumVariant {
                    payload: EnumVariantPayload::Tuple(args),
                    ..
                } => {
                    // The rewritten body should be a break
                    match &args[0] {
                        Expr::Break {
                            label: Some(lbl),
                            value: Some(err_val),
                        } => {
                            assert_eq!(lbl, &label);
                            assert!(is_result_err(err_val));
                        }
                        other => panic!("expected Break with Err inside Ok wrapper, got {other:?}"),
                    }
                }
                other => panic!("expected Ok variant, got {other:?}"),
            },
            other => panic!("expected Break, got {other:?}"),
        },
        other => panic!("expected Loop, got {other:?}"),
    }
}

#[test]
fn test_try_block_rewrites_return_none_to_break() {
    let tb = TryBlock {
        body: Expr::Return(Some(Box::new(wrap_in_option_none()))),
        result_type: TryResultType::Option,
    };
    let desugared = desugar_try_block(&tb);

    let label = match &desugared {
        Expr::Loop {
            label: Some(lbl), ..
        } => lbl.clone(),
        other => panic!("expected Loop, got {other:?}"),
    };

    match &desugared {
        Expr::Loop { body, .. } => match body.as_ref() {
            Expr::Break {
                value: Some(val), ..
            } => match val.as_ref() {
                Expr::EnumVariant {
                    payload: EnumVariantPayload::Tuple(args),
                    ..
                } => match &args[0] {
                    Expr::Break {
                        label: Some(lbl),
                        value: Some(none_val),
                    } => {
                        assert_eq!(lbl, &label);
                        assert!(is_option_none(none_val));
                    }
                    other => panic!("expected Break with None, got {other:?}"),
                },
                other => panic!("expected Some variant, got {other:?}"),
            },
            other => panic!("expected Break, got {other:?}"),
        },
        other => panic!("expected Loop, got {other:?}"),
    }
}

#[test]
fn test_try_block_preserves_non_error_return() {
    // `return Ok(v)` inside try should NOT be rewritten — it exits the function
    let tb = TryBlock {
        body: Expr::Return(Some(Box::new(wrap_in_result_ok(Expr::Literal(
            Value::u32(5),
        ))))),
        result_type: TryResultType::Result,
    };
    let desugared = desugar_try_block(&tb);

    match &desugared {
        Expr::Loop { body, .. } => match body.as_ref() {
            Expr::Break {
                value: Some(val), ..
            } => match val.as_ref() {
                Expr::EnumVariant {
                    payload: EnumVariantPayload::Tuple(args),
                    ..
                } => {
                    // return Ok(5) should pass through as Return (not Break)
                    assert!(
                        matches!(&args[0], Expr::Return(Some(_))),
                        "non-error return should be preserved, got {:?}",
                        args[0]
                    );
                }
                other => panic!("expected Ok variant, got {other:?}"),
            },
            other => panic!("expected Break, got {other:?}"),
        },
        other => panic!("expected Loop, got {other:?}"),
    }
}

// ----------------------------------------------------------------
// Helper tests
// ----------------------------------------------------------------

#[test]
fn test_wrap_in_result_ok_structure() {
    let expr = wrap_in_result_ok(Expr::Literal(Value::Bool(true)));
    match &expr {
        Expr::EnumVariant {
            enum_name,
            variant,
            payload: EnumVariantPayload::Tuple(args),
            ..
        } => {
            assert_eq!(enum_name, "Result");
            assert_eq!(variant, "Ok");
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Result::Ok, got {other:?}"),
    }
}

#[test]
fn test_wrap_in_result_err_structure() {
    let expr = wrap_in_result_err(Expr::Literal(Value::u32(1)));
    assert!(is_result_err(&expr));
}

#[test]
fn test_wrap_in_option_some_structure() {
    let expr = wrap_in_option_some(Expr::Literal(Value::u32(7)));
    match &expr {
        Expr::EnumVariant {
            enum_name,
            variant,
            payload: EnumVariantPayload::Tuple(args),
            ..
        } => {
            assert_eq!(enum_name, "Option");
            assert_eq!(variant, "Some");
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Option::Some, got {other:?}"),
    }
}

#[test]
fn test_wrap_in_option_none_structure() {
    let expr = wrap_in_option_none();
    assert!(is_option_none(&expr));
}

#[test]
fn test_try_result_type_eq() {
    assert_eq!(TryResultType::Result, TryResultType::Result);
    assert_eq!(TryResultType::Option, TryResultType::Option);
    assert_ne!(TryResultType::Result, TryResultType::Option);
}

#[test]
fn test_is_result_err_negative() {
    assert!(!is_result_err(&Expr::Literal(Value::Unit)));
    assert!(!is_result_err(&wrap_in_result_ok(Expr::Literal(
        Value::Unit
    ))));
}

#[test]
fn test_is_option_none_negative() {
    assert!(!is_option_none(&Expr::Literal(Value::Unit)));
    assert!(!is_option_none(&wrap_in_option_some(Expr::Literal(
        Value::Unit
    ))));
}

// ----------------------------------------------------------------
// Block-level desugaring (questions inside blocks)
// ----------------------------------------------------------------

#[test]
fn test_try_block_with_question_in_block_body() {
    // try { let x = expr?; x }
    // The Return(Err) inside the desugared ? should become Break
    let question_desugared = desugar_question_mark(&QuestionMarkOp {
        expr: Expr::Var {
            name: "r".to_string(),
            local_idx: 0,
        },
        try_label: None, // function-level initially
    });

    let block_body = Expr::Block {
        stmts: vec![crate::expr::Stmt::Let {
            pattern: Pattern::Binding {
                name: "x".to_string(),
                mutable: false,
                subpattern: None,
            },
            ty: None,
            init: Some(Box::new(question_desugared)),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        })),
    };

    let tb = TryBlock {
        body: block_body,
        result_type: TryResultType::Result,
    };
    let desugared = desugar_try_block(&tb);

    // Verify the structure has a Loop wrapping Break wrapping Ok(Block)
    assert!(matches!(&desugared, Expr::Loop { label: Some(_), .. }));
}

#[test]
fn test_fresh_labels_are_unique() {
    let l1 = fresh_try_label();
    let l2 = fresh_try_label();
    let l3 = fresh_try_label();
    assert_ne!(l1, l2);
    assert_ne!(l2, l3);
    assert_ne!(l1, l3);
}

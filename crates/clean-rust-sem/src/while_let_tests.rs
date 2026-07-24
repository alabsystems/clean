// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::expr::{EnumPatternPayload, EnumVariantPayload};
use crate::values::Value;

fn some_pattern(binding: &str) -> Pattern {
    Pattern::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
            name: binding.to_string(),
            mutable: false,
            subpattern: None,
        }]),
    }
}

fn ok_pattern(binding: &str) -> Pattern {
    Pattern::EnumVariant {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
            name: binding.to_string(),
            mutable: false,
            subpattern: None,
        }]),
    }
}

fn none_expr() -> Expr {
    Expr::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: EnumVariantPayload::Unit,
        type_args: vec![],
        const_args: vec![],
    }
}

fn some_expr(val: Expr) -> Expr {
    Expr::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: EnumVariantPayload::Tuple(vec![val]),
        type_args: vec![],
        const_args: vec![],
    }
}

fn err_expr(val: Expr) -> Expr {
    Expr::EnumVariant {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: EnumVariantPayload::Tuple(vec![val]),
        type_args: vec![],
        const_args: vec![],
    }
}

fn ok_expr(val: Expr) -> Expr {
    Expr::EnumVariant {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: EnumVariantPayload::Tuple(vec![val]),
        type_args: vec![],
        const_args: vec![],
    }
}

// -----------------------------------------------------------------------
// classify_pattern tests
// -----------------------------------------------------------------------

#[test]
fn test_classify_pattern_some_binding() {
    let pat = some_pattern("x");
    let classified = classify_pattern(&pat);
    assert_eq!(
        classified,
        WhileLetPattern::Some {
            binding: "x".to_string()
        }
    );
}

#[test]
fn test_classify_pattern_ok_binding() {
    let pat = ok_pattern("val");
    let classified = classify_pattern(&pat);
    assert_eq!(
        classified,
        WhileLetPattern::Ok {
            binding: "val".to_string()
        }
    );
}

#[test]
fn test_classify_pattern_custom_variant() {
    let pat = Pattern::EnumVariant {
        enum_name: "State".to_string(),
        variant: "Running".to_string(),
        payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
            name: "ctx".to_string(),
            mutable: false,
            subpattern: None,
        }]),
    };
    let classified = classify_pattern(&pat);
    assert_eq!(
        classified,
        WhileLetPattern::CustomVariant {
            enum_name: "State".to_string(),
            variant: "Running".to_string(),
            bindings: vec!["ctx".to_string()],
        }
    );
}

#[test]
fn test_classify_pattern_wildcard_is_other() {
    assert_eq!(classify_pattern(&Pattern::Wildcard), WhileLetPattern::Other);
}

#[test]
fn test_classify_pattern_unit_variant() {
    let pat = Pattern::EnumVariant {
        enum_name: "Poll".to_string(),
        variant: "Pending".to_string(),
        payload: EnumPatternPayload::Unit,
    };
    let classified = classify_pattern(&pat);
    assert_eq!(
        classified,
        WhileLetPattern::CustomVariant {
            enum_name: "Poll".to_string(),
            variant: "Pending".to_string(),
            bindings: vec![],
        }
    );
}

// -----------------------------------------------------------------------
// desugar_while_let tests
// -----------------------------------------------------------------------

#[test]
fn test_desugar_while_let_basic() {
    let desugared = desugar_while_let(
        some_pattern("x"),
        Expr::Var {
            name: "iter".to_string(),
            local_idx: 0,
        },
        Expr::Literal(Value::Unit),
        None,
        None,
    );
    // Should produce Loop { body: Match { ... } }
    assert!(matches!(desugared, Expr::Loop { label: None, .. }));
    if let Expr::Loop { body, .. } = &desugared {
        assert!(matches!(body.as_ref(), Expr::Match { arms, .. } if arms.len() == 2));
    }
}

#[test]
fn test_desugar_while_let_with_label() {
    let desugared = desugar_while_let(
        some_pattern("x"),
        Expr::Literal(Value::Unit),
        Expr::Literal(Value::Unit),
        None,
        Some("outer".to_string()),
    );
    if let Expr::Loop { label, .. } = &desugared {
        assert_eq!(label.as_deref(), Some("outer"));
    } else {
        panic!("expected Loop");
    }
}

#[test]
fn test_desugar_while_let_with_guard() {
    let guard = Expr::BinOp {
        op: crate::values::BinOp::Gt,
        left: Box::new(Expr::Var {
            name: "x".to_string(),
            local_idx: 0,
        }),
        right: Box::new(Expr::Literal(Value::u32(0))),
    };
    let desugared = desugar_while_let(
        some_pattern("x"),
        Expr::Literal(Value::Unit),
        Expr::Literal(Value::Unit),
        Some(guard),
        None,
    );
    if let Expr::Loop { body, .. } = &desugared {
        if let Expr::Match { arms, .. } = body.as_ref() {
            assert!(arms[0].guard.is_some(), "first arm should carry the guard");
            assert!(arms[1].guard.is_none(), "wildcard arm should have no guard");
        } else {
            panic!("expected Match inside Loop");
        }
    } else {
        panic!("expected Loop");
    }
}

#[test]
fn test_desugar_wildcard_arm_is_break() {
    let desugared = desugar_while_let(
        ok_pattern("v"),
        Expr::Literal(Value::Unit),
        Expr::Literal(Value::Unit),
        None,
        None,
    );
    if let Expr::Loop { body, .. } = &desugared {
        if let Expr::Match { arms, .. } = body.as_ref() {
            assert!(matches!(
                arms[1].body,
                Expr::Break {
                    label: None,
                    value: None
                }
            ));
        } else {
            panic!("expected Match inside Loop");
        }
    } else {
        panic!("expected Loop");
    }
}

// -----------------------------------------------------------------------
// analyze_while_let_termination tests
// -----------------------------------------------------------------------

#[test]
fn test_termination_some_vs_none_terminates() {
    let pat = WhileLetPattern::Some {
        binding: "x".to_string(),
    };
    let result = analyze_while_let_termination(&pat, &none_expr());
    assert_eq!(result, TerminationResult::Terminates);
}

#[test]
fn test_termination_some_vs_some_diverges() {
    let pat = WhileLetPattern::Some {
        binding: "x".to_string(),
    };
    let result = analyze_while_let_termination(&pat, &some_expr(Expr::Literal(Value::u32(42))));
    assert_eq!(result, TerminationResult::Diverges);
}

#[test]
fn test_termination_ok_vs_err_terminates() {
    let pat = WhileLetPattern::Ok {
        binding: "v".to_string(),
    };
    let result = analyze_while_let_termination(
        &pat,
        &err_expr(Expr::Literal(Value::Str("fail".to_string()))),
    );
    assert_eq!(result, TerminationResult::Terminates);
}

#[test]
fn test_termination_ok_vs_ok_diverges() {
    let pat = WhileLetPattern::Ok {
        binding: "v".to_string(),
    };
    let result = analyze_while_let_termination(&pat, &ok_expr(Expr::Literal(Value::u32(1))));
    assert_eq!(result, TerminationResult::Diverges);
}

#[test]
fn test_termination_custom_variant_mismatch_terminates() {
    let pat = WhileLetPattern::CustomVariant {
        enum_name: "State".to_string(),
        variant: "Running".to_string(),
        bindings: vec!["ctx".to_string()],
    };
    let scrutinee = Expr::EnumVariant {
        enum_name: "State".to_string(),
        variant: "Stopped".to_string(),
        payload: EnumVariantPayload::Unit,
        type_args: vec![],
        const_args: vec![],
    };
    assert_eq!(
        analyze_while_let_termination(&pat, &scrutinee),
        TerminationResult::Terminates
    );
}

#[test]
fn test_termination_custom_variant_match_diverges() {
    let pat = WhileLetPattern::CustomVariant {
        enum_name: "State".to_string(),
        variant: "Running".to_string(),
        bindings: vec![],
    };
    let scrutinee = Expr::EnumVariant {
        enum_name: "State".to_string(),
        variant: "Running".to_string(),
        payload: EnumVariantPayload::Unit,
        type_args: vec![],
        const_args: vec![],
    };
    assert_eq!(
        analyze_while_let_termination(&pat, &scrutinee),
        TerminationResult::Diverges
    );
}

#[test]
fn test_termination_variable_scrutinee_is_unknown() {
    let pat = WhileLetPattern::Some {
        binding: "x".to_string(),
    };
    let scrutinee = Expr::Var {
        name: "source".to_string(),
        local_idx: 0,
    };
    assert_eq!(
        analyze_while_let_termination(&pat, &scrutinee),
        TerminationResult::Unknown
    );
}

#[test]
fn test_termination_nested_outer_terminates() {
    let pat = WhileLetPattern::Nested {
        outer: Box::new(WhileLetPattern::Some {
            binding: "inner".to_string(),
        }),
        inner: Box::new(WhileLetPattern::Ok {
            binding: "v".to_string(),
        }),
    };
    // If the scrutinee is None, the outer Some pattern fails immediately
    assert_eq!(
        analyze_while_let_termination(&pat, &none_expr()),
        TerminationResult::Terminates
    );
}

#[test]
fn test_termination_nested_unknown_when_outer_matches() {
    let pat = WhileLetPattern::Nested {
        outer: Box::new(WhileLetPattern::Some {
            binding: "inner".to_string(),
        }),
        inner: Box::new(WhileLetPattern::Ok {
            binding: "v".to_string(),
        }),
    };
    // Scrutinee is Some(...) — outer matches, inner depends on runtime
    let scrutinee = some_expr(Expr::Literal(Value::Unit));
    assert_eq!(
        analyze_while_let_termination(&pat, &scrutinee),
        TerminationResult::Unknown
    );
}

#[test]
fn test_classify_nested_some_ok_pattern() {
    // Some(Ok(x)) pattern — inner is an enum variant inside the Some tuple
    let inner_ok = Pattern::EnumVariant {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
            name: "x".to_string(),
            mutable: false,
            subpattern: None,
        }]),
    };
    let outer = Pattern::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: EnumPatternPayload::Tuple(vec![inner_ok]),
    };
    let classified = classify_pattern(&outer);
    // The single tuple element is an EnumVariant, not a Binding, so
    // extract_payload_bindings returns empty. This routes through
    // CustomVariant (no single binding to satisfy the Some branch).
    assert!(matches!(classified, WhileLetPattern::CustomVariant { .. }));
}

#[test]
fn test_classify_struct_payload_variant() {
    let pat = Pattern::EnumVariant {
        enum_name: "Msg".to_string(),
        variant: "Data".to_string(),
        payload: EnumPatternPayload::Struct(vec![(
            "payload".to_string(),
            Pattern::Binding {
                name: "p".to_string(),
                mutable: false,
                subpattern: None,
            },
        )]),
    };
    let classified = classify_pattern(&pat);
    assert_eq!(
        classified,
        WhileLetPattern::CustomVariant {
            enum_name: "Msg".to_string(),
            variant: "Data".to_string(),
            bindings: vec!["p".to_string()],
        }
    );
}

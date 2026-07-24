// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for nested action lifting pre-pass (#1819).
//!
//! Verifies that `expand_nested_actions_expr` correctly recurses into
//! Match discriminees, StructLit field values/bases, and IfLet/IfDecidable
//! scrutinees to extract `<- expr` (LiftMethod) nodes.

use super::*;
use clean_parser::{
    DoElem, Span, SurfaceExpr, SurfaceFieldAssign, SurfaceLit, SurfaceMatchArm, SurfacePattern,
    UniverseExpr,
};

/// `<-` inside a match discriminee should be lifted.
/// `do return (match (<- Type) with | x => x)` should extract `<- Type` from
/// the match discriminee and produce a bind before the match.
#[test]
fn test_expand_nested_action_in_match_discriminee() {
    let sp = Span::dummy();
    let lift_type =
        SurfaceExpr::LiftMethod(sp, Box::new(SurfaceExpr::Universe(sp, UniverseExpr::Type)));
    let arm = SurfaceMatchArm {
        span: sp,
        pattern: SurfacePattern::Var("x".to_string()),
        body: SurfaceExpr::Ident(sp, "x".to_string()),
    };
    let match_expr = SurfaceExpr::Match(sp, None, Box::new(lift_type), vec![arm.clone()]);

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&match_expr, &mut counter, &mut lifted);

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from match discriminee"
    );
    match &lifted[0] {
        DoElem::Bind(_, binder, action) => {
            assert!(
                binder.name.starts_with("__do_lift_"),
                "expected __do_lift_N binder"
            );
            assert!(
                matches!(
                    action.as_ref(),
                    SurfaceExpr::Universe(_, UniverseExpr::Type)
                ),
                "expected Universe(Type) as lifted action"
            );
        }
        other => panic!("expected Bind from lift, got {other:?}"),
    }

    match &result {
        SurfaceExpr::Match(_, _, disc, arms) => {
            match disc.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert!(
                        name.starts_with("__do_lift_"),
                        "expected __do_lift_N ident, got {name}"
                    );
                }
                other => panic!("expected Ident(__do_lift_N) as new discriminee, got {other:?}"),
            }
            assert_eq!(arms.len(), 1, "arms should be unchanged");
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

/// `<-` inside struct literal field values should be lifted.
#[test]
fn test_expand_nested_action_in_struct_field() {
    let sp = Span::dummy();
    let lift_type =
        SurfaceExpr::LiftMethod(sp, Box::new(SurfaceExpr::Universe(sp, UniverseExpr::Type)));
    let struct_lit = SurfaceExpr::StructLit {
        span: sp,
        struct_type: None,
        base: None,
        fields: vec![SurfaceFieldAssign {
            span: sp,
            name: "val".to_string(),
            val: lift_type,
        }],
    };

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&struct_lit, &mut counter, &mut lifted);

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from struct field"
    );
    match &lifted[0] {
        DoElem::Bind(_, binder, _) => {
            assert!(binder.name.starts_with("__do_lift_"));
        }
        other => panic!("expected Bind, got {other:?}"),
    }

    match &result {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 1);
            match &fields[0].val {
                SurfaceExpr::Ident(_, name) => {
                    assert!(name.starts_with("__do_lift_"));
                }
                other => panic!("expected Ident(__do_lift_N), got {other:?}"),
            }
        }
        other => panic!("expected StructLit, got {other:?}"),
    }
}

/// `<-` inside struct literal base expression should be lifted.
#[test]
fn test_expand_nested_action_in_struct_base() {
    let sp = Span::dummy();
    let lift_base =
        SurfaceExpr::LiftMethod(sp, Box::new(SurfaceExpr::Ident(sp, "getState".to_string())));
    let struct_lit = SurfaceExpr::StructLit {
        span: sp,
        struct_type: None,
        base: Some(Box::new(lift_base)),
        fields: vec![SurfaceFieldAssign {
            span: sp,
            name: "val".to_string(),
            val: SurfaceExpr::Lit(sp, SurfaceLit::Nat(1)),
        }],
    };

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&struct_lit, &mut counter, &mut lifted);

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from struct base"
    );

    match &result {
        SurfaceExpr::StructLit { base, fields, .. } => {
            let base_expr = base.as_ref().expect("base should still be Some");
            match base_expr.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert!(name.starts_with("__do_lift_"));
                }
                other => panic!("expected Ident(__do_lift_N) as new base, got {other:?}"),
            }
            assert!(matches!(&fields[0].val, SurfaceExpr::Lit(_, _)));
        }
        other => panic!("expected StructLit, got {other:?}"),
    }
}

/// `<-` inside if-let scrutinee should be lifted.
#[test]
fn test_expand_nested_action_in_if_let_scrutinee() {
    let sp = Span::dummy();
    let lift_scrutinee = SurfaceExpr::LiftMethod(
        sp,
        Box::new(SurfaceExpr::Ident(sp, "getOption".to_string())),
    );
    let if_let = SurfaceExpr::IfLet(
        sp,
        SurfacePattern::Var("x".to_string()),
        Box::new(lift_scrutinee),
        Box::new(SurfaceExpr::Ident(sp, "x".to_string())),
        Box::new(SurfaceExpr::Ident(sp, "none".to_string())),
    );

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&if_let, &mut counter, &mut lifted);

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from if-let scrutinee"
    );

    match &result {
        SurfaceExpr::IfLet(_, _pat, scrutinee, _then, _else_) => match scrutinee.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert!(name.starts_with("__do_lift_"));
            }
            other => panic!("expected Ident(__do_lift_N), got {other:?}"),
        },
        other => panic!("expected IfLet, got {other:?}"),
    }
}

/// Multiple lifts in struct fields should produce sequential bindings.
#[test]
fn test_expand_multiple_lifts_in_struct_fields() {
    let sp = Span::dummy();
    let struct_lit = SurfaceExpr::StructLit {
        span: sp,
        struct_type: None,
        base: None,
        fields: vec![
            SurfaceFieldAssign {
                span: sp,
                name: "a".to_string(),
                val: SurfaceExpr::LiftMethod(
                    sp,
                    Box::new(SurfaceExpr::Ident(sp, "getA".to_string())),
                ),
            },
            SurfaceFieldAssign {
                span: sp,
                name: "b".to_string(),
                val: SurfaceExpr::LiftMethod(
                    sp,
                    Box::new(SurfaceExpr::Ident(sp, "getB".to_string())),
                ),
            },
        ],
    };

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&struct_lit, &mut counter, &mut lifted);

    assert_eq!(
        lifted.len(),
        2,
        "expected 2 lifted bindings from two struct fields"
    );
    assert_eq!(counter, 2);

    match &result {
        SurfaceExpr::StructLit { fields, .. } => {
            for (i, f) in fields.iter().enumerate() {
                match &f.val {
                    SurfaceExpr::Ident(_, name) => {
                        assert_eq!(name, &format!("__do_lift_{i}"));
                    }
                    other => panic!("field {i}: expected Ident, got {other:?}"),
                }
            }
        }
        other => panic!("expected StructLit, got {other:?}"),
    }
}

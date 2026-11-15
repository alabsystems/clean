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
        pattern: SurfacePattern::Var(SurfaceName::generated_path("x")),
        body: SurfaceExpr::Ident(sp, SurfaceName::generated_path("x")),
    };
    let match_expr = SurfaceExpr::Match(sp, None, Box::new(lift_type), vec![arm.clone()]);

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&match_expr, &mut counter, &mut lifted)
        .expect("no lift sits under a binder here");

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from match discriminee"
    );
    match &lifted[0] {
        DoElem::Bind(_, binder, action) => {
            assert!(
                binder
                    .name
                    .same_syntax(&SurfaceName::unspellable("__do_lift", 0)),
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
                        name.same_syntax(&SurfaceName::unspellable("__do_lift", 0)),
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
            name: SurfaceName::generated_path("val"),
            val: lift_type,
        }],
    };

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&struct_lit, &mut counter, &mut lifted)
        .expect("no lift sits under a binder here");

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from struct field"
    );
    match &lifted[0] {
        DoElem::Bind(_, binder, _) => {
            assert!(binder
                .name
                .same_syntax(&SurfaceName::unspellable("__do_lift", 0)));
        }
        other => panic!("expected Bind, got {other:?}"),
    }

    match &result {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 1);
            match &fields[0].val {
                SurfaceExpr::Ident(_, name) => {
                    assert!(name.same_syntax(&SurfaceName::unspellable("__do_lift", 0)));
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
    let lift_base = SurfaceExpr::LiftMethod(
        sp,
        Box::new(SurfaceExpr::Ident(
            sp,
            SurfaceName::generated_path("getState"),
        )),
    );
    let struct_lit = SurfaceExpr::StructLit {
        span: sp,
        struct_type: None,
        base: Some(Box::new(lift_base)),
        fields: vec![SurfaceFieldAssign {
            span: sp,
            name: SurfaceName::generated_path("val"),
            val: SurfaceExpr::Lit(sp, SurfaceLit::Nat(1)),
        }],
    };

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&struct_lit, &mut counter, &mut lifted)
        .expect("no lift sits under a binder here");

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
                    assert!(name.same_syntax(&SurfaceName::unspellable("__do_lift", 0)));
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
        Box::new(SurfaceExpr::Ident(
            sp,
            SurfaceName::generated_path("getOption"),
        )),
    );
    let if_let = SurfaceExpr::IfLet(
        sp,
        SurfacePattern::Var(SurfaceName::generated_path("x")),
        Box::new(lift_scrutinee),
        Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("x"))),
        Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("none"))),
    );

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&if_let, &mut counter, &mut lifted)
        .expect("no lift sits under a binder here");

    assert_eq!(
        lifted.len(),
        1,
        "expected 1 lifted binding from if-let scrutinee"
    );

    match &result {
        SurfaceExpr::IfLet(_, _pat, scrutinee, _then, _else_) => match scrutinee.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert!(name.same_syntax(&SurfaceName::unspellable("__do_lift", 0)));
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
                name: SurfaceName::generated_path("a"),
                val: SurfaceExpr::LiftMethod(
                    sp,
                    Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("getA"))),
                ),
            },
            SurfaceFieldAssign {
                span: sp,
                name: SurfaceName::generated_path("b"),
                val: SurfaceExpr::LiftMethod(
                    sp,
                    Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("getB"))),
                ),
            },
        ],
    };

    let mut counter = 0usize;
    let mut lifted = Vec::new();
    let result = ElabCtx::expand_nested_actions_expr(&struct_lit, &mut counter, &mut lifted)
        .expect("no lift sits under a binder here");

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
                        assert_eq!(name.name(), &Name::anon().str("__do_lift").num(i as u64));
                    }
                    other => panic!("field {i}: expected Ident, got {other:?}"),
                }
            }
        }
        other => panic!("expected StructLit, got {other:?}"),
    }
}

/// G53 (ledger (123)): `while (← c) do body` is Lean's `repeat if (← c)
/// then body else break`, so the lifted bind sits INSIDE the loop and runs
/// every iteration. The pre-pass used to hoist it ahead of the loop.
#[test]
fn test_expand_while_condition_lift_stays_inside_the_loop() {
    let sp = Span::dummy();
    let get = SurfaceExpr::Ident(sp, SurfaceName::generated_path("get"));
    let cond = SurfaceExpr::App(
        sp,
        Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("ok"))),
        vec![SurfaceArg::positional(SurfaceExpr::LiftMethod(
            sp,
            Box::new(get),
        ))],
    );
    let body = vec![DoElem::Expr(
        sp,
        Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("step"))),
    )];
    let elems = vec![DoElem::While(sp, Box::new(cond), body)];
    let out = ElabCtx::expand_seq_nested_actions(&elems, &mut 0).expect("lifts");

    let [DoElem::Repeat(_, loop_body)] = out.as_slice() else {
        panic!("a lifting `while` condition must become one `repeat`: {out:?}");
    };
    let [DoElem::Bind(_, binder, _), DoElem::If(_, cond, then_branch, Some(else_branch))] =
        loop_body.as_slice()
    else {
        panic!("the loop body must bind the condition's action, then test it: {loop_body:?}");
    };
    assert!(binder
        .name
        .same_syntax(&SurfaceName::unspellable("__do_lift", 0)));
    assert!(
        !matches!(cond.as_ref(), SurfaceExpr::LiftMethod(..)),
        "the condition reads the lifted name"
    );
    assert!(matches!(then_branch.as_slice(), [DoElem::Expr(..)]));
    assert!(matches!(else_branch.as_slice(), [DoElem::Break(_)]));

    // A condition that lifts nothing keeps the direct `while` lowering.
    let plain = vec![DoElem::While(
        sp,
        Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("c"))),
        Vec::new(),
    )];
    let out = ElabCtx::expand_seq_nested_actions(&plain, &mut 0).expect("no lifts");
    assert!(matches!(out.as_slice(), [DoElem::While(..)]));
}

/// G52 (ledger (122)): a lift in a `let rec` value is refused with Lean's
/// message, never hoisted out of the recursive value.
#[test]
fn test_expand_let_rec_value_lift_is_refused() {
    let sp = Span::dummy();
    let value = SurfaceExpr::LiftMethod(
        sp,
        Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("e"))),
    );
    let binder = SurfaceBinder::new("k", None, SurfaceBinderInfo::Explicit);
    let elems = vec![
        DoElem::LetRec(sp, vec![(binder, Box::new(value))]),
        DoElem::Expr(
            sp,
            Box::new(SurfaceExpr::Ident(sp, SurfaceName::generated_path("k"))),
        ),
    ];
    let err = ElabCtx::expand_seq_nested_actions(&elems, &mut 0)
        .expect_err("Lean refuses a lift over a `let rec`");
    assert!(
        err.to_string()
            .contains("cannot lift `(<- ...)` over a binder"),
        "{err}"
    );
}

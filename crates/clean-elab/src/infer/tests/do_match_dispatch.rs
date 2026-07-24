// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for untested elab_do dispatch paths (#1816).
//!
//! Covers: empty arms error, multi-discriminant dispatch, multi-discriminant
//! arm error, constructor-order bail-outs (wildcard not last, duplicate ctor),
//! trailing let/bind errors, and do-if without else branch.

use super::*;
use clean_parser::{
    DoElem, DoMatchArm, Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceLit,
    SurfacePattern,
};

fn expr_contains_prod_mk_levels(expr: &Expr, left: &Level, right: &Level) -> bool {
    match expr.kind() {
        ExprKind::Const(name, levels) => {
            name.to_string() == "Prod.mk"
                && levels.len() == 2
                && &levels[0] == left
                && &levels[1] == right
        }
        ExprKind::App(fun, arg) => {
            expr_contains_prod_mk_levels(fun, left, right)
                || expr_contains_prod_mk_levels(arg, left, right)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_prod_mk_levels(ty, left, right)
                || expr_contains_prod_mk_levels(body, left, right)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            expr_contains_prod_mk_levels(ty, left, right)
                || expr_contains_prod_mk_levels(value, left, right)
                || expr_contains_prod_mk_levels(body, left, right)
        }
        ExprKind::Proj(_, _, value) | ExprKind::MData(_, value) => {
            expr_contains_prod_mk_levels(value, left, right)
        }
        _ => false,
    }
}

fn nat_axiom_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();
    env
}

fn two_nat_axiom_env() -> Environment {
    let mut env = Environment::with_prelude();
    for name in &["x", "y"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
        })
        .unwrap();
    }
    env
}

fn two_polymorphic_type_axiom_env() -> Environment {
    let mut env = Environment::with_prelude();
    for (name, level) in [
        ("x", Level::succ(Level::zero())),
        ("y", Level::succ(Level::succ(Level::zero()))),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(level),
        })
        .unwrap();
    }
    env
}

// === Test 1: Empty arms error (elab_do_match.rs:60-64) ===

#[test]
fn test_elab_do_match_empty_arms_returns_not_implemented() {
    let env = nat_axiom_env();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![], // empty arms
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    let err = result.expect_err("empty match arms should fail");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("match with no arms"),
        "expected 'match with no arms' error, got: {msg}"
    );
}

#[test]
#[serial_test::serial]
fn test_elab_do_match_empty_discriminants_fail_closed_without_context_or_sorry_leaks() {
    use clean_kernel::sorry::{reset_sorry_counter, sorry_count, synthetic_sorry_count};

    let env = nat_axiom_env();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let sentinel = ctx.push_local("sentinel".to_string(), nat.clone());
    ctx.push_local_instance(sentinel, nat.clone());
    ctx.instance_cache
        .insert("sentinel-cache".to_string(), Expr::fvar(sentinel));
    ctx.current_expected_type = Some(nat.clone());
    ctx.match_dependent_motive = Some(nat.clone());
    ctx.match_dependent_motive_indices = 1;
    ctx.match_index_discriminating_punit = Some(Level::zero());

    let locals_before = ctx.locals.clone();
    let let_values_before = ctx.local_let_values.clone();
    let shared_before = ctx.shared_if_let_scrutinees.clone();
    let instances_before = ctx.local_instances.clone();
    let instance_cache_before = ctx.instance_cache.clone();
    let expected_before = ctx.current_expected_type.clone();
    let recursive_before = format!("{:?}", ctx.recursive_def_ctx);
    let motive_before = ctx.match_dependent_motive.clone();
    let motive_indices_before = ctx.match_dependent_motive_indices;
    let punit_before = ctx.match_index_discriminating_punit.clone();
    let universes_before = ctx.universe_params.clone();
    let pending_before = ctx.pending_level_assigns.borrow().clone();
    let holes_before = ctx.hole_names.clone();
    let meta_depth_before = ctx.metas.scope_depth();

    let arm = DoMatchArm {
        span: Span::dummy(),
        patterns: vec![SurfacePattern::Wildcard],
        body: vec![DoElem::Expr(
            Span::dummy(),
            Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
        )],
    };

    reset_sorry_counter();
    let total_before = sorry_count();
    let synthetic_before = synthetic_sorry_count();
    let result = ctx.elab_do_match(&[], &[arm]);

    assert!(
        matches!(&result, Err(ElabError::NotImplemented(message)) if message.contains("no discriminants")),
        "empty do-match discriminants must fail explicitly, got {result:?}"
    );
    assert_eq!(sorry_count(), total_before, "failure emitted a sorry term");
    assert_eq!(
        synthetic_sorry_count(),
        synthetic_before,
        "failure emitted a synthetic sorry term"
    );
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.local_let_values, let_values_before);
    assert_eq!(ctx.shared_if_let_scrutinees, shared_before);
    assert_eq!(ctx.local_instances, instances_before);
    assert_eq!(ctx.instance_cache, instance_cache_before);
    assert_eq!(ctx.current_expected_type, expected_before);
    assert_eq!(format!("{:?}", ctx.recursive_def_ctx), recursive_before);
    assert_eq!(ctx.match_dependent_motive, motive_before);
    assert_eq!(ctx.match_dependent_motive_indices, motive_indices_before);
    assert_eq!(ctx.match_index_discriminating_punit, punit_before);
    assert_eq!(ctx.universe_params, universes_before);
    assert_eq!(*ctx.pending_level_assigns.borrow(), pending_before);
    assert_eq!(ctx.hole_names, holes_before);
    assert_eq!(ctx.metas.scope_depth(), meta_depth_before);
}

// === Test 2: Multi-discriminant dispatch (elab_do_match.rs:71-87) ===
// Prod.mk construction inserts implicit type args (#2956 fix).
// Multi-discriminant with wildcard pattern desugars to let binding.

#[test]
fn test_elab_do_match_multi_discriminant_reaches_prod_mk_path() {
    let env = two_nat_axiom_env();

    // do match x, y with | _, _ => 0
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![
                SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
                SurfaceExpr::Ident(Span::dummy(), "y".to_string()),
            ],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::Wildcard],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "multi-discriminant do-match with wildcard should elaborate, got {result:?}"
    );
}

// === Test 3: Multi-discriminant ctor arm error (elab_do_match_arm:329-335) ===
// Multi-discriminant with per-component ctor patterns: Prod.mk succeeds but
// elab_do_match_arm rejects multi-pattern arms (not yet implemented).

#[test]
fn test_elab_do_match_multi_discriminant_ctor_arm_returns_error() {
    let env = two_nat_axiom_env();

    // do match x, y with | Nat.zero, Nat.zero => 0  (2 patterns per arm)
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![
                SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
                SurfaceExpr::Ident(Span::dummy(), "y".to_string()),
            ],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![
                        SurfacePattern::Ctor("Nat.zero".to_string(), vec![]),
                        SurfacePattern::Ctor("Nat.zero".to_string(), vec![]),
                    ],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    // Prod.mk construction succeeds, but multi-pattern arms hit NotImplemented
    let err = result.expect_err("multi-discriminant ctor match should produce an error");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("multi-discriminant") || msg.contains("NotImplemented"),
        "expected multi-discriminant or NotImplemented error, got: {msg}"
    );
}

// === Test 4: Unknown constructor name (elab_do_match.rs) ===
// An unresolvable dotted name in pattern position is a HARD error, matching
// Lean 4's `unknown identifier 'Nat.nonexistent'`. Dotted names are never
// binding patterns (only simple atomic identifiers become pattern variables,
// which still route through SurfacePattern::Var). The former "fall back to
// sequential casesOn" behavior was a silent miscompilation: the arms were
// applied POSITIONALLY as casesOn minors, installing a different program
// than the one written.

#[test]
fn test_elab_do_match_unknown_ctor_is_hard_error() {
    let env = nat_axiom_env();

    // do match n with | Nat.nonexistent => 0 | _ => 1
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor("Nat.nonexistent".to_string(), vec![])],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    let err = result.expect_err("unknown dotted ctor pattern must be rejected");
    assert!(
        matches!(&err, ElabError::UnknownIdent(name) if name == "Nat.nonexistent"),
        "expected UnknownIdent(Nat.nonexistent), got {err:?}"
    );
}

// === Test 5: Constructor-order bail-out: wildcard not last (ctor_order.rs:60-62) ===

#[test]
fn test_elab_do_match_wildcard_not_last_falls_back_to_sequential() {
    let env = nat_axiom_env();

    // do match n with | _ => 0 | Nat.zero => 1
    // Wildcard not in last position → try_build_ctor_ordered returns None,
    // falls back to sequential processing
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor("Nat.zero".to_string(), vec![])],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    // The wildcard-first arm triggers sequential fallback which still works
    // because the first wildcard arm catches everything
    assert!(
        result.is_ok(),
        "wildcard-not-last should fall back to sequential and still elaborate, got {result:?}"
    );
}

// === Test 6: Constructor-order bail-out: duplicate ctor (ctor_order.rs:75-77) ===

#[test]
fn test_elab_do_match_duplicate_ctor_falls_back_to_sequential() {
    let env = nat_axiom_env();

    // do match n with | Nat.zero => 0 | Nat.zero => 1 | _ => 2
    // Duplicate Nat.zero → try_build_ctor_ordered returns None
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor("Nat.zero".to_string(), vec![])],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor("Nat.zero".to_string(), vec![])],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    // Duplicate ctor triggers sequential fallback; may succeed or fail
    // depending on elaboration path, but should not panic
    match &result {
        Ok(_) => {} // sequential fallback succeeded — fine
        Err(e) => {
            let msg = format!("{e:?}");
            // Should not be a panic or ICE — only expected elaboration errors
            assert!(
                !msg.contains("panic") && !msg.contains("internal"),
                "duplicate ctor should not cause internal error, got: {msg}"
            );
        }
    }
}

// === Test 7: Multi-discriminant with Prod.mk wrapping (#2956 fix) ===
// Prod.mk implicit type args are now inserted correctly.

#[test]
fn test_elab_do_match_multi_discriminant_prod_mk_elaborates() {
    let env = two_nat_axiom_env();

    // do match x, y with | _, _ => 0
    // Multi-discriminant folds discriminants into Prod.mk with implicit type args
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![
                SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
                SurfaceExpr::Ident(Span::dummy(), "y".to_string()),
            ],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::Wildcard],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let expr = ctx
        .elaborate(&surface)
        .expect("multi-discriminant Prod.mk should elaborate with implicit type args");
    // Verify the output contains Prod.mk (hierarchical Name: "Prod" then "mk")
    let s = format!("{expr:?}");
    assert!(
        s.contains("\"Prod\"") && s.contains("\"mk\""),
        "multi-discriminant output should contain Prod.mk name components, got: {s}"
    );
}

#[test]
fn test_elab_do_match_polymorphic_discriminants_use_exact_prod_levels() {
    let env = two_polymorphic_type_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![
                SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
                SurfaceExpr::Ident(Span::dummy(), "y".to_string()),
            ],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::Wildcard],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let expr = ctx
        .elaborate(&surface)
        .expect("polymorphic multi-discriminant do-match should elaborate");
    let type_1 = Level::succ(Level::zero());
    let type_2 = Level::succ(type_1.clone());
    assert!(
        expr_contains_prod_mk_levels(&expr, &type_1, &type_2),
        "Prod.mk must retain the exact Type 1/Type 2 discriminant universes: {expr:?}"
    );
    let _ = ctx
        .infer_type(&expr)
        .expect("kernel checks polymorphic multi-discriminant do-match");
}

// === Test 8: Trailing let binding error (elab_do.rs:214-217) ===

#[test]
fn test_elab_do_trailing_let_returns_error() {
    let env = Environment::with_prelude();

    // do let x := 42  (no continuation after let)
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Let(
            Span::dummy(),
            SurfaceBinder::new("x", None, SurfaceBinderInfo::Explicit),
            Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42))),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    let err = result.expect_err("trailing let in do block should fail");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("cannot end with a let"),
        "expected 'cannot end with a let binding' error, got: {msg}"
    );
}

// === Test 9: Trailing bind error (elab_do.rs:220-222) ===

#[test]
fn test_elab_do_trailing_bind_returns_error() {
    let env = Environment::with_prelude();

    // do x <- Type  (no continuation after bind)
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Bind(
            Span::dummy(),
            SurfaceBinder::new("x", None, SurfaceBinderInfo::Explicit),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "Type".to_string())),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    let err = result.expect_err("trailing bind in do block should fail");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("cannot end with a bind"),
        "expected 'cannot end with a bind' error, got: {msg}"
    );
}

// === Test 10: elab_do_if without else branch (elab_do_if.rs:99-103) ===

#[test]
fn test_elab_do_if_no_else_produces_pure_unit() {
    let env = Environment::with_prelude();

    // do if True then return Unit.unit
    // No else branch → desugars else to Pure.pure Unit.unit
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::If(
            Span::dummy(),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "True".to_string())),
            vec![DoElem::Return(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
            )],
            None, // no else branch
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "do-if without else should elaborate (else defaults to Pure.pure Unit.unit), got {result:?}"
    );
}

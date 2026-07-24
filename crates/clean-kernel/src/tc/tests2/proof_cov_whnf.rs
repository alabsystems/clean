// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — `whnf_core_no_delta` reduction paths.
//!
//! Covers:
//! - `whnf_core_no_delta(e, cheap_proj=true)` — delta-skipping, beta, zeta, FVar, MData
//! - `whnf_core_no_delta(e, cheap_proj=false)` — full projection reduction without delta

use std::sync::Arc;

use super::*;

// ===== whnf_core_no_delta tests =====
// whnf_core_no_delta (tc/mod.rs:2476) is the partial WHNF that skips delta reduction.
// This function has a dead-code suppression attribute in production — a Phase 1 prerequisite.
// These tests verify its delta-skipping behavior.

/// Test whnf_core_no_delta skips constant unfolding.
/// A defined constant should NOT be unfolded by whnf_core_no_delta.
#[test]
fn test_whnf_core_no_delta_skips_const_unfolding() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Define id := λ (x : Type). x
    let id_body = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let id_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: vec![],
        type_: id_type,
        value: id_body,
        is_reducible: true,
    })
    .expect("adding 'id' definition to environment should succeed");

    let tc = TypeChecker::new(&env);

    let id_const = Expr::const_(Name::from_string("id"), vec![]);

    // whnf_core_no_delta should NOT unfold `id` — it stays as Const
    let result = tc.whnf_core_no_delta(&id_const, true);
    assert!(
        matches!(&result.kind, ExprKind::Const(name, _) if name.to_string() == "id"),
        "whnf_core_no_delta should not unfold constants, got: {result:?}"
    );

    // In contrast, whnf_core SHOULD unfold `id` (delta reduction)
    let result_full = tc.whnf_core(&id_const);
    assert!(
        matches!(&result_full.kind, ExprKind::Lam(_, _, _)),
        "whnf_core should unfold constants via delta reduction, got: {result_full:?}"
    );
}

/// Regression for #1474: projection reduction in no-delta mode must not trigger delta unfolding.
#[test]
fn test_whnf_core_no_delta_proj_does_not_unfold_struct_const() {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("adding 'p' axiom to environment should succeed");

    let pair_name = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);
    let pair_mk_ty = Expr::arrow(Expr::prop(), pair_ref.clone());
    let p_const = Expr::const_(Name::from_string("p"), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: pair_mk_ty,
            }],
        }],
    })
    .expect("adding 'Pair' inductive type to environment should succeed");

    let pair_value = Expr::app(
        Expr::const_(Name::from_string("Pair.mk"), vec![]),
        p_const.clone(),
    );
    let pair_const = Name::from_string("pairVal");
    env.add_decl(Declaration::Definition {
        name: pair_const.clone(),
        level_params: vec![],
        type_: pair_ref,
        value: pair_value,
        is_reducible: true,
    })
    .expect("adding 'pairVal' definition to environment should succeed");

    let tc = TypeChecker::new(&env);
    let proj = Expr::proj(
        pair_name.clone(),
        0,
        Expr::const_(pair_const.clone(), vec![]),
    );

    let no_delta = tc.whnf_core_no_delta(&proj, true);
    assert!(
        matches!(
            &no_delta.kind,
            ExprKind::Proj(struct_name, idx, inner)
                if struct_name == &pair_name
                    && *idx == 0
                    && matches!(&inner.kind, ExprKind::Const(name, _) if name == &pair_const)
        ),
        "whnf_core_no_delta projection should stay stuck on const without delta, got: {no_delta:?}"
    );

    let full = tc.whnf(&proj);
    assert_eq!(
        full, p_const,
        "full whnf should still unfold + project to the field"
    );
}

/// Test whnf_core_no_delta performs beta reduction.
#[test]
fn test_whnf_core_no_delta_does_beta() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (λ (x : Type). x) Prop → should beta-reduce to Prop
    let id_lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let app = Expr::app(id_lam, Expr::prop());

    let result = tc.whnf_core_no_delta(&app, true);
    assert!(
        matches!(&result.kind, ExprKind::Sort(l) if l.is_zero()),
        "Beta reduction should produce Prop (Sort(0)), got: {result:?}"
    );
}

/// Test whnf_core_no_delta performs zeta reduction (let-binding).
#[test]
fn test_whnf_core_no_delta_does_zeta() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // let x : Type := Prop in x → should reduce to Prop
    let let_expr = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    );

    let result = tc.whnf_core_no_delta(&let_expr, true);
    assert!(
        matches!(&result.kind, ExprKind::Sort(l) if l.is_zero()),
        "Zeta reduction should produce Prop (Sort(0)), got: {result:?}"
    );
}

/// Test whnf_core_no_delta unfolds let-bound FVars.
#[test]
fn test_whnf_core_no_delta_unfolds_let_fvar() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Create an FVar with a let-binding value
    let fvar_id = tc.ctx.borrow_mut().push_let(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(), // let-bound to Prop
    );
    let fvar = Expr::fvar(fvar_id);

    let result = tc.whnf_core_no_delta(&fvar, true);
    assert!(
        matches!(&result.kind, ExprKind::Sort(l) if l.is_zero()),
        "Let-bound FVar should unfold to Prop, got: {result:?}"
    );
}

/// Test whnf_core_no_delta leaves non-let FVars unchanged.
#[test]
fn test_whnf_core_no_delta_keeps_non_let_fvar() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Create an FVar WITHOUT a let-binding value
    let fvar_id =
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("y"), Expr::type_(), BinderInfo::Default);
    let fvar = Expr::fvar(fvar_id);

    let result = tc.whnf_core_no_delta(&fvar, true);
    assert!(
        matches!(&result.kind, ExprKind::FVar(id) if *id == fvar_id),
        "Non-let FVar should stay unchanged, got: {result:?}"
    );
}

/// Test whnf_core_no_delta strips MData wrappers.
#[test]
fn test_whnf_core_no_delta_strips_mdata() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // MData wrapping Prop → should reduce to Prop
    let mdata = Expr::mdata(vec![], Expr::prop());

    let result = tc.whnf_core_no_delta(&mdata, true);
    assert!(
        matches!(&result.kind, ExprKind::Sort(l) if l.is_zero()),
        "MData should be transparent, got: {result:?}"
    );
}

/// Test whnf_core_no_delta does NOT strip Squash wrappers.
///
/// Squash is a type former (Squash A : SProp), not metadata. Unlike MData,
/// Squash(A) and A have different types, so WHNF must not reduce through it.
/// See #2164.
#[test]
fn test_whnf_core_no_delta_preserves_squash() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Squash wrapping Prop — should NOT reduce to Prop
    let squash = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::prop())));

    let result = tc.whnf_core_no_delta(&squash, true);
    assert!(
        matches!(&result.kind, ExprKind::Squash(_)),
        "Squash should be opaque in WHNF, got: {result:?}"
    );
}

/// Test full WHNF does NOT strip Squash wrappers.
/// Squash(Type) should remain Squash(Type), not reduce to Type. See #2164.
#[test]
fn test_whnf_preserves_squash() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let squash = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::type_())));

    let result = tc.whnf(&squash);
    assert!(
        matches!(&result.kind, ExprKind::Squash(_)),
        "full WHNF should preserve Squash, got: {result:?}"
    );
}

/// Test is_def_eq does NOT conflate Squash(a) with a.
///
/// Squash(Type) : SProp and Type : Sort 1 have different types, so they
/// must not be definitionally equal. See #2164.
#[test]
fn test_is_def_eq_squash_opaque() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = Expr::type_();
    let squash = Expr::from_kind(ExprKind::Squash(Arc::new(inner.clone())));

    assert!(
        !tc.is_def_eq(&squash, &inner),
        "Squash(Type) should NOT be def-eq to Type"
    );
    assert!(
        !tc.is_def_eq(&inner, &squash),
        "Type should NOT be def-eq to Squash(Type)"
    );
}

/// Test is_def_eq: Squash(a) =?= Squash(a) still holds (structural equality).
#[test]
fn test_is_def_eq_squash_structural() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = Expr::prop();
    let squash1 = Expr::from_kind(ExprKind::Squash(Arc::new(inner.clone())));
    let squash2 = Expr::from_kind(ExprKind::Squash(Arc::new(inner)));

    assert!(
        tc.is_def_eq(&squash1, &squash2),
        "Squash(Prop) should be def-eq to Squash(Prop)"
    );
}

/// Test nested Squash: Squash(Squash(a)) !=?= a but Squash(Squash(a)) =?= Squash(Squash(a)).
#[test]
fn test_is_def_eq_nested_squash_opaque() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = Expr::prop();
    let squash1 = Expr::from_kind(ExprKind::Squash(Arc::new(inner.clone())));
    let squash2 = Expr::from_kind(ExprKind::Squash(Arc::new(squash1.clone())));

    assert!(
        !tc.is_def_eq(&squash2, &inner),
        "Squash(Squash(Prop)) should NOT be def-eq to Prop"
    );
    // But nested Squash should equal itself
    let squash2b = Expr::from_kind(ExprKind::Squash(Arc::new(squash1)));
    assert!(
        tc.is_def_eq(&squash2, &squash2b),
        "Squash(Squash(Prop)) should be def-eq to Squash(Squash(Prop))"
    );
}

// ===== whnf_core_no_delta(e, false) tests =====
// whnf_core_no_delta(e, cheap_proj=false) is Phase 5 of is_def_eq.
// It applies full projection reduction without delta.
// Previously had zero direct tests.

/// Test whnf_core_no_delta(e, false): reduces projection on constructor application.
#[test]
fn test_whnf_core_no_delta_full_proj_proj_reduction() {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("adding 'p' axiom to environment should succeed");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("adding 'q' axiom to environment should succeed");

    // inductive Pair : Type where | mk : Prop → Prop → Pair
    let pair_name = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::pi(BinderInfo::Default, Expr::prop(), pair_ref),
                ),
            }],
        }],
    })
    .expect("adding 'Pair' inductive type with two-field constructor should succeed");

    let tc = TypeChecker::new(&env);

    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let pair_val = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Pair.mk"), vec![]),
            p.clone(),
        ),
        q.clone(),
    );

    // Proj(Pair, 0, Pair.mk p q) should reduce to p
    let proj0 = Expr::proj(pair_name.clone(), 0, pair_val.clone());
    let result0 = tc.whnf_core_no_delta(&proj0, false);
    assert_eq!(result0, p, "Proj(Pair, 0, Pair.mk p q) should reduce to p");

    // Proj(Pair, 1, Pair.mk p q) should reduce to q
    let proj1 = Expr::proj(pair_name.clone(), 1, pair_val);
    let result1 = tc.whnf_core_no_delta(&proj1, false);
    assert_eq!(result1, q, "Proj(Pair, 1, Pair.mk p q) should reduce to q");
}

/// Test whnf_core_no_delta_full_proj: does NOT unfold definitions.
#[test]
fn test_whnf_core_no_delta_full_proj_no_delta() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Definition {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("adding 'myProp' definition to environment should succeed");

    let tc = TypeChecker::new(&env);

    let my_prop = Expr::const_(Name::from_string("myProp"), vec![]);
    let result = tc.whnf_core_no_delta(&my_prop, false);

    // Should NOT unfold myProp — it's a Const, no delta
    assert!(
        matches!(&result.kind, ExprKind::Const(name, _) if name.to_string() == "myProp"),
        "whnf_core_no_delta(e, false) should not unfold constants, got: {result:?}"
    );
}

/// Test whnf_core_no_delta(e, false): performs beta reduction.
#[test]
fn test_whnf_core_no_delta_full_proj_beta() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (λ (x : Type). x) Prop → should beta-reduce to Prop
    let app = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    );

    let result = tc.whnf_core_no_delta(&app, false);
    assert!(
        matches!(&result.kind, ExprKind::Sort(l) if l.is_zero()),
        "Beta reduction should produce Prop, got: {result:?}"
    );
}

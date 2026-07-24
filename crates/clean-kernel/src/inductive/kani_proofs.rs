// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Kani bounded model checking harnesses for positivity checker.
/// Verify soundness-critical properties for all inputs up to a bound.
///
/// Run with: cargo kani --features kani -p clean-kernel --harness <harness_name>
use super::*;
use crate::expr::BinderInfo;
use std::sync::Arc;

/// Helper: single-name positivity check for Kani harnesses.
fn check_pos(name: &Name, expr: &Expr, param_count: u32) -> Result<(), InductiveError> {
    check_positivity(name, expr, param_count, &[name])
}

/// Leak a value to prevent CBMC from unwinding recursive Arc<Name> drops.
fn leak_expr(e: Expr) {
    std::mem::forget(e);
}
fn leak_name(n: Name) {
    std::mem::forget(n);
}

/// Verify that negative occurrences are detected.
/// The classic negative occurrence: (I → X) → R where I is the inductive.
/// This pattern would allow false proofs via Girard's paradox if not rejected.
///
/// Uses numeric names (Name::anon().num(N)) to avoid Arc<str> allocation
/// and string comparison that causes CBMC state explosion with from_string().
#[kani::proof]
#[kani::unwind(5)]
fn verify_negative_occurrence_detected() {
    // Use numeric name to avoid Arc<str> — CBMC-friendly
    let ind_name = Name::anon().num(1);

    // Build expression: (T → Type) → T
    // This is a classic non-positive occurrence (T appears left of inner arrow)
    let t_const: Expr = Expr::from_kind(ExprKind::Const(ind_name.clone(), Default::default()));
    let type_ = Expr::type_();

    // Inner: T → Type
    let inner_pi: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_const.clone()),
        Arc::new(type_.clone()),
    )
    .into();

    // Outer: (T → Type) → T
    let ctor_type: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner_pi),
        Arc::new(t_const.clone()),
    )
    .into();

    // This should be rejected as non-positive
    let result = check_pos(&ind_name, &ctor_type, 0);
    assert!(
        result.is_err(),
        "Negative occurrence (T → Type) → T must be rejected"
    );
    leak_expr(ctor_type);
    leak_expr(t_const);
    leak_expr(type_);
    leak_name(ind_name);
}

/// Verify that positive occurrences are accepted.
/// Standard patterns like succ : Nat → Nat should be allowed.
///
/// Uses numeric names to avoid CBMC state explosion from Arc<str>.
#[kani::proof]
#[kani::unwind(5)]
fn verify_positive_occurrence_accepted() {
    // Use numeric name — CBMC-friendly (avoids Arc<str>)
    let ind_name = Name::anon().num(2);
    let nat_const: Expr = Expr::from_kind(ExprKind::Const(ind_name.clone(), Default::default()));

    // Build expression: Nat → Nat (like succ constructor)
    let ctor_type: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(nat_const.clone()),
        Arc::new(nat_const.clone()),
    )
    .into();

    // This should be accepted - the inductive appears directly, not negatively
    let result = check_pos(&ind_name, &ctor_type, 0);
    assert!(
        result.is_ok(),
        "Positive occurrence Nat → Nat must be accepted"
    );
    leak_expr(ctor_type);
    leak_expr(nat_const);
    leak_name(ind_name);
}

/// Verify strictly positive nested occurrences.
/// Pattern: (X → T) → T is strictly positive (T in codomain, not domain of inner arrow)
///
/// Uses numeric names to avoid CBMC state explosion from Arc<str>.
#[kani::proof]
#[kani::unwind(5)]
fn verify_strictly_positive_nested() {
    // Use numeric names — CBMC-friendly (avoids Arc<str>)
    let ind_name = Name::anon().num(1);
    let t_const: Expr = Expr::from_kind(ExprKind::Const(ind_name.clone(), Default::default()));

    // Some other type X (different numeric id)
    let x_name = Name::anon().num(2);
    let x_const: Expr = Expr::from_kind(ExprKind::Const(x_name.clone(), Default::default()));

    // Inner: X → T (T in codomain - this is fine)
    let inner_pi: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(x_const.clone()),
        Arc::new(t_const.clone()),
    )
    .into();

    // Outer: (X → T) → T
    let ctor_type: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner_pi),
        Arc::new(t_const.clone()),
    )
    .into();

    // This should be accepted - T only appears in codomains (strictly positive)
    let result = check_pos(&ind_name, &ctor_type, 0);
    assert!(
        result.is_ok(),
        "Strictly positive (X → T) → T must be accepted"
    );
    leak_expr(ctor_type);
    leak_expr(t_const);
    leak_expr(x_const);
    leak_name(ind_name);
    leak_name(x_name);
}

/// Verify mentions_name correctly detects Const name occurrences.
/// Tests direct Const matching and non-matching for BVar/Sort primitives.
///
/// Uses numeric names to avoid CBMC state explosion from Arc<str>.
#[kani::proof]
#[kani::unwind(5)]
fn verify_mentions_name_detects_const() {
    // Use numeric names — CBMC-friendly
    let target_name = Name::anon().num(10);
    let other_name = Name::anon().num(20);

    // Const with target name should be detected
    let expr_with_target: Expr =
        Expr::from_kind(ExprKind::Const(target_name.clone(), Default::default()));
    assert!(
        mentions_name(&expr_with_target, &target_name),
        "mentions_name should detect Const with target name"
    );

    // Const with different name should not match
    let expr_other: Expr = Expr::from_kind(ExprKind::Const(other_name.clone(), Default::default()));
    assert!(
        !mentions_name(&expr_other, &target_name),
        "mentions_name should not match different name"
    );

    // BVar should never mention a name
    let bvar: Expr = Expr::from_kind(ExprKind::BVar(0));
    assert!(
        !mentions_name(&bvar, &target_name),
        "BVar should never mention a name"
    );

    // Sort should never mention a name
    let sort = Expr::type_();
    assert!(
        !mentions_name(&sort, &target_name),
        "Sort should never mention a name"
    );
    leak_name(target_name);
    leak_name(other_name);
    leak_expr(expr_with_target);
    leak_expr(expr_other);
    leak_expr(bvar);
    leak_expr(sort);
}

/// Verify App with inductive applied to arguments is handled correctly.
/// When the inductive T is applied to args (App(T, arg)), the args must not
/// mention T at all (they are checked with `check_no_negative_occurrence`).
///
/// Uses numeric names to avoid CBMC state explosion from Arc<str>.
#[kani::proof]
#[kani::unwind(5)]
fn verify_app_inductive_args_checked() {
    // Use numeric names — CBMC-friendly
    let ind_name = Name::anon().num(1);
    let t_const: Expr = Expr::from_kind(ExprKind::Const(ind_name.clone(), Default::default()));

    let x_name = Name::anon().num(2);
    let x_const: Expr = Expr::from_kind(ExprKind::Const(x_name.clone(), Default::default()));

    // Build: App(T, X) → T
    // Structure: Pi(_, App(T, X), T)
    // This is like: constructor : T A → T where T is applied to type A
    let t_applied: Expr = Expr::from_kind(ExprKind::App(
        Arc::new(t_const.clone()),
        Arc::new(x_const.clone()),
    ));
    let ctor_type: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_applied),
        Arc::new(t_const.clone()),
    )
    .into();

    // This should be accepted - T applied to X where X doesn't mention T
    let result = check_pos(&ind_name, &ctor_type, 0);
    assert!(
        result.is_ok(),
        "App(T, X) → T must be accepted (X doesn't mention T)"
    );

    // Now test negative case: App(T, (T → X)) → T
    // Structure: Pi(_, App(T, Pi(_, T, X)), T)
    // The argument (T → X) to T mentions T - this should be rejected
    let bad_arg: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_const.clone()),
        Arc::new(x_const.clone()),
    )
    .into();
    let t_with_bad_arg: Expr =
        Expr::from_kind(ExprKind::App(Arc::new(t_const.clone()), Arc::new(bad_arg)));
    let bad_ctor_type: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_with_bad_arg),
        Arc::new(t_const.clone()),
    )
    .into();

    // This should be rejected - argument to T mentions T
    let result = check_pos(&ind_name, &bad_ctor_type, 0);
    assert!(
        result.is_err(),
        "App(T, (T → X)) → T must be rejected (arg mentions T)"
    );
    leak_name(ind_name);
    leak_name(x_name);
    leak_expr(t_const);
    leak_expr(x_const);
    leak_expr(ctor_type);
    leak_expr(bad_ctor_type);
}

/// Verify nested non-positive occurrence detection.
/// Pattern: ((T → X) → Y) → T - T appears in nested negative position
///
/// Uses numeric names to avoid CBMC state explosion from Arc<str>.
#[kani::proof]
#[kani::unwind(5)]
fn verify_nested_negative_detected() {
    // Use numeric names — CBMC-friendly
    let ind_name = Name::anon().num(1);
    let t_const: Expr = Expr::from_kind(ExprKind::Const(ind_name.clone(), Default::default()));

    let x_name = Name::anon().num(2);
    let x_const: Expr = Expr::from_kind(ExprKind::Const(x_name.clone(), Default::default()));

    let y_name = Name::anon().num(3);
    let y_const: Expr = Expr::from_kind(ExprKind::Const(y_name.clone(), Default::default()));

    // Innermost: T → X (T in negative position)
    let inner1: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_const.clone()),
        Arc::new(x_const.clone()),
    )
    .into();

    // Middle: (T → X) → Y
    let inner2: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner1),
        Arc::new(y_const.clone()),
    )
    .into();

    // Outer: ((T → X) → Y) → T
    let ctor_type: Expr = ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner2),
        Arc::new(t_const.clone()),
    )
    .into();

    // This should be rejected - T appears in domain of inner arrow
    let result = check_pos(&ind_name, &ctor_type, 0);
    assert!(
        result.is_err(),
        "Nested negative ((T → X) → Y) → T must be rejected"
    );
    leak_name(ind_name);
    leak_name(x_name);
    leak_name(y_name);
    leak_expr(t_const);
    leak_expr(x_const);
    leak_expr(y_const);
    leak_expr(ctor_type);
}

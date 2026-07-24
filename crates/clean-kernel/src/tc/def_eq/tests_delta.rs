// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Delta failure cache and lazy delta reduction tests.
//!
//! Split from `tests.rs` for the 500-line file size limit (#2548).

use super::*;
use crate::env::Environment;
use crate::expr::BinderInfo;
use crate::level::Level;

// ============================================================================
// Delta failure cache tests (#1783)
// ============================================================================

/// Helper: add a Regular(height) definition to the environment.
fn add_regular_def(env: &mut Environment, name: &str, ty: Expr, value: Expr, height: u32) {
    let mut info =
        crate::env::ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.reducibility = crate::env::Reducibility::Regular(height);
    env.extend_constants_unchecked(std::iter::once(info));
}

#[test]
fn test_args_failure_cache_starts_empty() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "delta failure cache should start empty"
    );
}

/// When two same-name Regular constants have non-def-eq arguments,
/// `lazy_delta_step_equal` records the failure. A subsequent is_def_eq
/// call on the same pair will skip the redundant argument comparison.
#[test]
fn test_args_failure_cache_populated_on_failed_args() {
    let mut env = Environment::new();

    // f := fun (x : Prop) => x, a Regular(0) definition
    let f_body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_regular_def(
        &mut env,
        "f",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        f_body,
        0,
    );

    let tc = TypeChecker::new(&env);

    // f(Prop) vs f(Type) -- same head (f), same height, but args differ.
    // The lazy delta step will try is_def_eq_args_only, fail, and cache it.
    let t = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::prop());
    let s = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::type_());

    // They are not def-eq (Prop != Type as arguments)
    // But after delta unfolding, f(Prop) = Prop and f(Type) = Type, still not equal
    let result = tc.is_def_eq(&t, &s);
    assert!(!result, "f(Prop) should not be def-eq to f(Type)");

    // The failure cache should have been populated during the lazy delta loop
    assert!(
        tc.args_failure_cache_entries() > 0,
        "delta failure cache should have entries after failed same-head arg comparison"
    );
}

// ============================================================================
// quick_is_def_eq Sort arm regression tests (#1663)
// ============================================================================

/// Sort comparison: identical universe levels are definitionally equal.
/// The Sort arm in `quick_is_def_eq` delegates to `levels_eq`.
#[test]
fn test_quick_is_def_eq_sort_same_level_returns_true() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Sort(0) vs Sort(0) — Prop vs Prop
    let prop_a = Expr::sort(Level::zero());
    let prop_b = Expr::sort(Level::zero());
    assert_eq!(
        tc.quick_is_def_eq(&prop_a, &prop_b),
        Some(true),
        "Sort(0) should be def-eq to Sort(0)"
    );

    // Sort(1) vs Sort(1) — Type vs Type
    let type_a = Expr::sort(Level::succ(Level::zero()));
    let type_b = Expr::sort(Level::succ(Level::zero()));
    assert_eq!(
        tc.quick_is_def_eq(&type_a, &type_b),
        Some(true),
        "Sort(1) should be def-eq to Sort(1)"
    );

    // Sort(2) vs Sort(2)
    let sort2_a = Expr::sort(Level::succ(Level::succ(Level::zero())));
    let sort2_b = Expr::sort(Level::succ(Level::succ(Level::zero())));
    assert_eq!(
        tc.quick_is_def_eq(&sort2_a, &sort2_b),
        Some(true),
        "Sort(2) should be def-eq to Sort(2)"
    );
}

/// Sort comparison: different universe levels are NOT definitionally equal.
#[test]
fn test_quick_is_def_eq_sort_different_levels_returns_false() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Sort(0) vs Sort(1) — Prop vs Type
    let prop = Expr::sort(Level::zero());
    let type_ = Expr::sort(Level::succ(Level::zero()));
    assert_eq!(
        tc.quick_is_def_eq(&prop, &type_),
        Some(false),
        "Sort(0) should NOT be def-eq to Sort(1)"
    );

    // Sort(1) vs Sort(2)
    let sort1 = Expr::sort(Level::succ(Level::zero()));
    let sort2 = Expr::sort(Level::succ(Level::succ(Level::zero())));
    assert_eq!(
        tc.quick_is_def_eq(&sort1, &sort2),
        Some(false),
        "Sort(1) should NOT be def-eq to Sort(2)"
    );

    // Sort(0) vs Sort(2)
    let prop = Expr::sort(Level::zero());
    let sort2 = Expr::sort(Level::succ(Level::succ(Level::zero())));
    assert_eq!(
        tc.quick_is_def_eq(&prop, &sort2),
        Some(false),
        "Sort(0) should NOT be def-eq to Sort(2)"
    );
}

/// Sort comparison: parametric universe levels (Level::param).
/// Same parameter name should be def-eq; different names should not.
#[test]
fn test_quick_is_def_eq_sort_parametric_levels() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let v = Name::from_string("v");

    // Sort(u) vs Sort(u) — same parameter
    let sort_u_a = Expr::sort(Level::param(u.clone()));
    let sort_u_b = Expr::sort(Level::param(u.clone()));
    assert_eq!(
        tc.quick_is_def_eq(&sort_u_a, &sort_u_b),
        Some(true),
        "Sort(u) should be def-eq to Sort(u)"
    );

    // Sort(u) vs Sort(v) — different parameters
    let sort_u = Expr::sort(Level::param(u));
    let sort_v = Expr::sort(Level::param(v));
    assert_eq!(
        tc.quick_is_def_eq(&sort_u, &sort_v),
        Some(false),
        "Sort(u) should NOT be def-eq to Sort(v)"
    );
}

/// Sort comparison: quick_is_def_eq returns None for non-Sort pairs,
/// confirming the Sort arm only fires when both sides are Sort.
#[test]
fn test_quick_is_def_eq_sort_vs_non_sort_returns_none() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let sort = Expr::sort(Level::zero());
    let lit = Expr::nat_lit(0);

    assert_eq!(
        tc.quick_is_def_eq(&sort, &lit),
        None,
        "Sort vs Lit should return None (unhandled by quick_is_def_eq)"
    );
    assert_eq!(
        tc.quick_is_def_eq(&lit, &sort),
        None,
        "Lit vs Sort should return None (unhandled by quick_is_def_eq)"
    );
}

// ============================================================================
// quick_is_def_eq MData arm regression tests (#1663)
// ============================================================================

/// MData comparison: same metadata and same inner expr are def-eq.
#[test]
fn test_quick_is_def_eq_mdata_same_metadata_same_inner() {
    use crate::expr::MDataValue;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let md_a = Expr::mdata(
        vec![(Name::from_string("tag"), MDataValue::Nat(1))],
        Expr::nat_lit(42),
    );
    let md_b = Expr::mdata(
        vec![(Name::from_string("tag"), MDataValue::Nat(1))],
        Expr::nat_lit(42),
    );
    assert_eq!(
        tc.quick_is_def_eq(&md_a, &md_b),
        Some(true),
        "MData with same metadata and same inner should be def-eq"
    );
}

/// MData comparison: different metadata but same inner expr should still be
/// def-eq because MData is transparent (metadata is ignored for def-eq).
#[test]
fn test_quick_is_def_eq_mdata_different_metadata_same_inner() {
    use crate::expr::MDataValue;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let md_a = Expr::mdata(
        vec![(Name::from_string("tag_a"), MDataValue::Nat(1))],
        Expr::prop(),
    );
    let md_b = Expr::mdata(
        vec![(Name::from_string("tag_b"), MDataValue::Nat(999))],
        Expr::prop(),
    );
    assert_eq!(
        tc.quick_is_def_eq(&md_a, &md_b),
        Some(true),
        "MData with different metadata but same inner should be def-eq (metadata is transparent)"
    );
}

/// MData comparison: different inner expressions should NOT be def-eq.
#[test]
fn test_quick_is_def_eq_mdata_different_inner_returns_false() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let md_a = Expr::mdata(vec![], Expr::nat_lit(1));
    let md_b = Expr::mdata(vec![], Expr::nat_lit(2));
    assert_eq!(
        tc.quick_is_def_eq(&md_a, &md_b),
        Some(false),
        "MData with different inner expressions should NOT be def-eq"
    );
}

/// MData comparison: nested MData layers — inner recursion should resolve.
#[test]
fn test_quick_is_def_eq_mdata_nested_layers() {
    use crate::expr::MDataValue;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Single-wrapped vs double-wrapped with same leaf
    let single = Expr::mdata(
        vec![(Name::from_string("a"), MDataValue::Nat(1))],
        Expr::nat_lit(7),
    );
    let double = Expr::mdata(
        vec![(Name::from_string("b"), MDataValue::Nat(2))],
        Expr::mdata(
            vec![(Name::from_string("c"), MDataValue::Nat(3))],
            Expr::nat_lit(7),
        ),
    );

    // quick_is_def_eq on (MData, MData) recurses on inner expressions.
    // single's inner is Lit(7), double's inner is MData(c, Lit(7)).
    // That recurse hits (Lit, MData) which returns None from quick_is_def_eq,
    // so this goes through full is_def_eq_impl which handles it.
    // The top-level is_def_eq should succeed.
    assert!(
        tc.is_def_eq(&single, &double),
        "Nested MData wrapping the same leaf should be def-eq via full is_def_eq"
    );
}

/// MData vs non-MData: quick_is_def_eq now handles asymmetric MData directly
/// by stripping the wrapper and recursing. This ensures MData transparency at
/// every recursive comparison level, not just at the top-level WHNF. (#3134)
#[test]
fn test_quick_is_def_eq_mdata_vs_non_mdata_strips_wrapper() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let wrapped = Expr::mdata(vec![], Expr::nat_lit(5));
    let bare = Expr::nat_lit(5);

    // quick_is_def_eq now strips MData wrapper and recurses
    assert_eq!(
        tc.quick_is_def_eq(&wrapped, &bare),
        Some(true),
        "MData vs non-MData should strip wrapper and return Some(true)"
    );

    // Reverse direction
    assert_eq!(
        tc.quick_is_def_eq(&bare, &wrapped),
        Some(true),
        "non-MData vs MData should strip wrapper and return Some(true)"
    );

    // Full is_def_eq should also succeed
    assert!(
        tc.is_def_eq(&wrapped, &bare),
        "MData-wrapped expr should be def-eq to bare expr"
    );

    // Different inner expressions should still fail
    let wrapped_other = Expr::mdata(vec![], Expr::nat_lit(6));
    assert_eq!(
        tc.quick_is_def_eq(&wrapped_other, &bare),
        Some(false),
        "MData wrapping different value should not be def-eq"
    );
}

// ============================================================================
// Delta failure cache tests (#1783)
// ============================================================================

/// The delta failure cache is cleared when transparency mode changes,
/// since different transparency levels can yield different unfolding results.
#[test]
fn test_args_failure_cache_cleared_on_transparency_change() {
    let mut env = Environment::new();

    let f_body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_regular_def(
        &mut env,
        "g",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        f_body,
        0,
    );

    let mut tc = TypeChecker::new(&env);

    let t = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::prop());
    let s = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::type_());

    let _ = tc.is_def_eq(&t, &s);
    assert!(
        tc.args_failure_cache_entries() > 0,
        "precondition: cache should be populated"
    );

    tc.set_transparency(TransparencyMode::All);
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "delta failure cache should be cleared after transparency change"
    );
}

// ============================================================================
// lazy_delta_reduction height-based unfolding tests (#1659)
// ============================================================================

/// When two constants have different heights, the HIGHER-height one is
/// unfolded first. Both reduce to Prop, so is_def_eq should succeed.
#[test]
fn test_lazy_delta_higher_height_unfolded_first_reaches_equality() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "high", Expr::prop(), Expr::prop(), 10);
    add_regular_def(&mut env, "low", Expr::prop(), Expr::prop(), 2);
    let tc = TypeChecker::new(&env);
    let high_expr = Expr::const_(Name::from_string("high"), vec![]);
    let low_expr = Expr::const_(Name::from_string("low"), vec![]);
    assert!(tc.is_def_eq(&high_expr, &low_expr));
}

/// Equal height, different names: both are unfolded.
#[test]
fn test_lazy_delta_equal_height_different_names_both_unfolded() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "alpha", Expr::prop(), Expr::prop(), 5);
    add_regular_def(&mut env, "beta", Expr::prop(), Expr::prop(), 5);
    let tc = TypeChecker::new(&env);
    let alpha_expr = Expr::const_(Name::from_string("alpha"), vec![]);
    let beta_expr = Expr::const_(Name::from_string("beta"), vec![]);
    assert!(tc.is_def_eq(&alpha_expr, &beta_expr));
}

/// Equal height, same name, matching args: resolved without unfolding.
#[test]
fn test_lazy_delta_equal_height_same_name_args_match_no_unfold() {
    let mut env = Environment::new();
    let id_body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_regular_def(
        &mut env,
        "id_fn",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        id_body,
        0,
    );
    let tc = TypeChecker::new(&env);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("id_fn"), vec![]),
        Expr::prop(),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("id_fn"), vec![]),
        Expr::prop(),
    );
    assert!(tc.is_def_eq(&lhs, &rhs));
    assert_eq!(tc.args_failure_cache_entries(), 0);
}

/// Chain unfolding through heights: top(h=2) -> mid(h=1) -> base(h=0) -> Prop.
#[test]
fn test_lazy_delta_chain_unfolding_through_heights() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "base", Expr::prop(), Expr::prop(), 0);
    add_regular_def(
        &mut env,
        "mid",
        Expr::prop(),
        Expr::const_(Name::from_string("base"), vec![]),
        1,
    );
    add_regular_def(
        &mut env,
        "top",
        Expr::prop(),
        Expr::const_(Name::from_string("mid"), vec![]),
        2,
    );
    let tc = TypeChecker::new(&env);
    let top_expr = Expr::const_(Name::from_string("top"), vec![]);
    let base_expr = Expr::const_(Name::from_string("base"), vec![]);
    assert!(tc.is_def_eq(&top_expr, &base_expr));
}

/// Different heights and different values: correctly returns false.
#[test]
fn test_lazy_delta_different_heights_different_values_not_def_eq() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "prop_def", Expr::prop(), Expr::prop(), 5);
    add_regular_def(&mut env, "type_def", Expr::type_(), Expr::type_(), 3);
    let tc = TypeChecker::new(&env);
    let prop_expr = Expr::const_(Name::from_string("prop_def"), vec![]);
    let type_expr = Expr::const_(Name::from_string("type_def"), vec![]);
    assert!(!tc.is_def_eq(&prop_expr, &type_expr));
}

/// Asymmetric chain depths converge: 3-level chain vs direct definition.
#[test]
fn test_lazy_delta_asymmetric_chain_depths_converge() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "direct_prop", Expr::prop(), Expr::prop(), 0);
    add_regular_def(&mut env, "c0", Expr::prop(), Expr::prop(), 0);
    add_regular_def(
        &mut env,
        "c1",
        Expr::prop(),
        Expr::const_(Name::from_string("c0"), vec![]),
        1,
    );
    add_regular_def(
        &mut env,
        "c2",
        Expr::prop(),
        Expr::const_(Name::from_string("c1"), vec![]),
        2,
    );
    add_regular_def(
        &mut env,
        "c3",
        Expr::prop(),
        Expr::const_(Name::from_string("c2"), vec![]),
        3,
    );
    let tc = TypeChecker::new(&env);
    let c3_expr = Expr::const_(Name::from_string("c3"), vec![]);
    let direct_expr = Expr::const_(Name::from_string("direct_prop"), vec![]);
    assert!(tc.is_def_eq(&c3_expr, &direct_expr));
    assert!(tc.is_def_eq(&direct_expr, &c3_expr));
}

// ============================================================================
// Monadic def-eq hook (Track Q)
// ============================================================================

/// `is_def_eq` recognizes `Pure.pure (Except ε) α a` as definitionally equal
/// to `Except.ok ε α a`. The monad-class heads are axioms (no delta value), so
/// without the `try_monad_reduce` hook in the lazy-delta loop the two stuck
/// consts `Pure.pure` and `Except.ok` would report DefUnknown and the
/// comparison would fail — exactly the do-block `pure x` / vector lane-fold
/// `rfl` regression this fix targets.
#[test]
fn test_def_eq_pure_over_except_equals_except_ok() {
    let mut env = Environment::new();
    env.init_id().expect("init_id");
    env.init_state_t().expect("init_state_t");
    env.init_except_t().expect("init_except_t");
    env.init_monad_classes().expect("init_monad_classes");
    let tc = TypeChecker::new(&env);

    let eps = Expr::prop();
    let except_eps = Expr::apps(
        Expr::const_(Name::from_string("Except"), vec![Level::zero()]),
        vec![eps.clone()],
    );
    let alpha = Expr::type_();
    let value = Expr::prop();
    let pure = Expr::apps(
        Expr::const_(
            Name::from_string("Pure.pure"),
            vec![Level::zero(), Level::zero()],
        ),
        vec![except_eps, alpha.clone(), value.clone()],
    );
    let except_ok = Expr::apps(
        Expr::const_(Name::from_string("Except.ok"), vec![Level::zero()]),
        vec![eps, alpha, value],
    );

    assert!(tc.is_def_eq(&pure, &except_ok));
    assert!(tc.is_def_eq(&except_ok, &pure));
}

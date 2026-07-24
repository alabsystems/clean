// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Expr, FVarId, Level, Name};
use proptest::prelude::*;

fn closed_expr_strategy() -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![
        Just(Expr::prop()),
        Just(Expr::type_()),
        Just(Expr::sort(Level::succ(Level::zero()))),
        Just(Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0))),
        Just(Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop())),
    ];
    leaf.prop_recursive(4, 64, 8, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(f, a)| Expr::app(f, a)),
            inner
                .clone()
                .prop_map(|body| Expr::lam(BinderInfo::Default, Expr::prop(), body)),
            (inner.clone(), inner.clone()).prop_map(|(ty, body)| Expr::pi(
                BinderInfo::Default,
                ty,
                body
            )),
        ]
    })
}

fn lambda_body_with_bvar_strategy() -> impl Strategy<Value = Expr> {
    prop_oneof![
        Just(Expr::bvar(0)),
        closed_expr_strategy().prop_map(|arg| Expr::app(Expr::bvar(0), arg)),
        closed_expr_strategy().prop_map(|f| Expr::app(f, Expr::bvar(0))),
        closed_expr_strategy().prop_map(|ty| Expr::lam(BinderInfo::Default, ty, Expr::bvar(0))),
    ]
}

proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(32))]

    #[test]
    fn prop_instantiate_closed_identity(e in closed_expr_strategy(), v in closed_expr_strategy()) {
        prop_assume!(!e.has_loose_bvars());
        prop_assume!(!v.has_loose_bvars());
        let result = e.clone().instantiate(&v);
        prop_assert_eq!(&result, &e,
            "instantiate should be identity on closed expressions");
        prop_assert!(!result.has_loose_bvars(),
            "instantiate should not introduce loose bvars");
    }

    #[test]
    fn prop_instantiate_bvar_zero(v in closed_expr_strategy()) {
        prop_assume!(!v.has_loose_bvars());
        let result = Expr::bvar(0).instantiate(&v);
        prop_assert_eq!(&result, &v,
            "instantiate(BVar(0), v) should return v");
    }

    #[test]
    fn prop_instantiate_bvar_decrement(v in closed_expr_strategy(), idx in 1u32..8) {
        prop_assume!(!v.has_loose_bvars());
        let result = Expr::bvar(idx).instantiate(&v);
        prop_assert_eq!(&result, &Expr::bvar(idx - 1),
            "instantiate(BVar(n), v) should decrement for n > 0");
    }

    /// Test that instantiate leaves bound variables in lambda bodies alone.
    /// The spec now uses depth tracking via instantiate_at in
    /// crates/clean-verify/src/spec.rs (Part of #643), matching the kernel.
    /// This guards against regressions to the old lift-based definition.
    /// See: reports/research/2026-02-01-r3-subst-commutes-lift-analysis.md
    #[test]
    fn prop_instantiate_preserves_lambda_bound_vars(
        ty in closed_expr_strategy(),
        body in lambda_body_with_bvar_strategy(),
        v in closed_expr_strategy()
    ) {
        prop_assume!(!v.has_loose_bvars());
        prop_assume!(!ty.has_loose_bvars());
        let identity = Expr::lam(BinderInfo::Default, ty.clone(), body.clone());
        let result = identity.clone().instantiate(&v);
        // The body's bvar(0) should stay as bvar(0), not become the substituted value.
        let expected = Expr::lam(BinderInfo::Default, ty.instantiate(&v), body.clone());
        prop_assert_eq!(&result, &expected,
            "instantiate should preserve bound variables in lambda bodies");
    }
}

// ============================================================
// Phase 1a: Proptest equivalents of Kani timeout harnesses (#982)
// Migrated from designs/2026-03-04-982-proptest-alternative.md
//
// These replace 54 Kani harnesses that timeout on recursive ADTs.
// Kani's CBMC backend cannot handle recursive types (Name, Level, Expr)
// without SAT explosion. Proptest exercises real production code paths.
// ============================================================

/// Strategy for compound expressions with binders and levels.
/// Generates deeper expressions than closed_expr_strategy() by including
/// Sort with level parameters, Let expressions, and nested binders.
fn compound_expr_strategy() -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![
        Just(Expr::prop()),
        Just(Expr::type_()),
        Just(Expr::sort(Level::succ(Level::zero()))),
        Just(Expr::sort(Level::succ(Level::succ(Level::zero())))),
        Just(Expr::nat_lit(0)),
        Just(Expr::nat_lit(42)),
        Just(Expr::str_lit("x")),
    ];
    leaf.prop_recursive(4, 64, 8, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(f, a)| Expr::app(f, a)),
            inner
                .clone()
                .prop_map(|body| Expr::lam(BinderInfo::Default, Expr::prop(), body)),
            inner
                .clone()
                .prop_map(|body| Expr::lam(BinderInfo::Implicit, Expr::type_(), body)),
            (inner.clone(), inner.clone()).prop_map(|(ty, body)| Expr::pi(
                BinderInfo::Default,
                ty,
                body
            )),
            (inner.clone(), inner.clone()).prop_map(|(val, body)| Expr::let_named(
                Name::anon(),
                Expr::prop(),
                val,
                body,
                false
            )),
        ]
    })
}

/// Strategy for expressions containing a specific FVar, used for
/// abstract_fvar roundtrip testing.
fn expr_with_fvar_strategy(fvar_id: FVarId) -> impl Strategy<Value = Expr> {
    let fvar = Expr::fvar(fvar_id);
    let leaf = prop_oneof![Just(fvar.clone()), Just(Expr::prop()), Just(Expr::type_()),];
    leaf.prop_recursive(3, 32, 6, move |inner| {
        let fvar_inner = Expr::fvar(fvar_id);
        prop_oneof![
            (inner.clone(), Just(fvar_inner.clone())).prop_map(|(f, a)| Expr::app(f, a)),
            (Just(fvar_inner), inner.clone()).prop_map(|(f, a)| Expr::app(f, a)),
            inner
                .clone()
                .prop_map(|body| Expr::lam(BinderInfo::Default, Expr::prop(), body)),
            (inner.clone(), inner.clone()).prop_map(|(ty, body)| Expr::pi(
                BinderInfo::Default,
                ty,
                body
            )),
        ]
    })
}

proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(256))]

    // ================================================================
    // THE KEY PROPERTY from #982:
    //   instantiate(lift(1, e), v) == e   for closed e
    //
    // Kani equivalents: verify_inst_lift_identity, verify_inst_lift_identity_app,
    // verify_inst_lift_identity_lambda, verify_inst_lift_identity_pi,
    // verify_roundtrip_app_minimal (all timeout at 300s)
    // ================================================================

    #[test]
    fn prop_instantiate_lift_roundtrip(
        e in closed_expr_strategy(),
        v in closed_expr_strategy()
    ) {
        prop_assume!(!e.has_loose_bvars());
        let lifted = e.lift(1);
        let roundtrip = lifted.instantiate(&v);
        prop_assert_eq!(&roundtrip, &e,
            "instantiate(lift(1, e), v) should equal e for closed e");
    }

    // ================================================================
    // abstract_fvar(id, e).instantiate(FVar(id)) == e
    //
    // Kani equivalents: verify_abstract_instantiate_roundtrip_fvar,
    // verify_abstract_instantiate_roundtrip_app, _lam, _pi, _nested,
    // _other_fvar, _app_mixed, _fvar_with_bvar (all timeout)
    // ================================================================

    #[test]
    fn prop_abstract_instantiate_roundtrip(
        e in closed_expr_strategy()
    ) {
        prop_assume!(!e.has_loose_bvars());
        let id = FVarId::new(99999);
        // For closed e with no FVar(id), abstract_fvar is identity,
        // then instantiate is identity. This is the base case.
        let abstracted = e.abstract_fvar(id);
        let roundtrip = abstracted.instantiate(&Expr::fvar(id));
        prop_assert_eq!(&roundtrip, &e,
            "abstract_fvar then instantiate should roundtrip for closed e");
    }

    /// Test abstract/instantiate roundtrip on expressions that actually contain
    /// the free variable being abstracted.
    #[test]
    fn prop_abstract_instantiate_roundtrip_with_fvar(
        e in expr_with_fvar_strategy(FVarId::new(12345))
    ) {
        prop_assume!(!e.has_loose_bvars());
        let id = FVarId::new(12345);
        let abstracted = e.abstract_fvar(id);
        let roundtrip = abstracted.instantiate(&Expr::fvar(id));
        prop_assert_eq!(&roundtrip, &e,
            "abstract_fvar then instantiate should roundtrip when FVar present");
    }

    // ================================================================
    // Lift composition: lift(m, lift(n, e)) == lift(n+m, e)  for closed e
    //
    // Kani equivalents: verify_lift_composition, verify_lift_composition_app,
    // verify_bvar_lift_bounds (all timeout)
    // ================================================================

    #[test]
    fn prop_lift_composition_general(
        e in closed_expr_strategy(),
        n in 1u32..8,
        m in 1u32..8
    ) {
        prop_assume!(!e.has_loose_bvars());
        let lift_then_lift = e.lift(n).lift(m);
        let lift_sum = e.lift(n.saturating_add(m));
        prop_assert_eq!(&lift_then_lift, &lift_sum,
            "lift(m, lift(n, e)) should equal lift(n+m, e) for closed e");
    }

    // ================================================================
    // Compound expressions: instantiate(lift(1, e), v) == e for lam/pi/let
    //
    // Kani equivalents: verify_inst_lift_identity_app, _lambda, _pi,
    // verify_instantiate_types (all timeout)
    // ================================================================

    #[test]
    fn prop_instantiate_lift_roundtrip_compound(
        e in compound_expr_strategy(),
        v in closed_expr_strategy()
    ) {
        prop_assume!(!e.has_loose_bvars());
        let lifted = e.lift(1);
        let roundtrip = lifted.instantiate(&v);
        prop_assert_eq!(&roundtrip, &e,
            "instantiate(lift(1, e), v) should equal e for compound closed e");
    }

    // ================================================================
    // Lift preserves closedness
    // ================================================================

    #[test]
    fn prop_lift_preserves_closedness(
        e in closed_expr_strategy(),
        n in 1u32..16
    ) {
        prop_assume!(!e.has_loose_bvars());
        let lifted = e.lift(n);
        // For closed expressions, lift is identity, so still closed
        prop_assert!(!lifted.has_loose_bvars(),
            "lift should preserve closedness for closed expressions");
        prop_assert_eq!(&lifted, &e,
            "lift(n) on closed expression should be identity");
    }

    // ================================================================
    // Instantiate preserves closedness when substitution is closed
    // ================================================================

    #[test]
    fn prop_instantiate_preserves_closedness(
        e in closed_expr_strategy(),
        v in closed_expr_strategy()
    ) {
        prop_assume!(!e.has_loose_bvars());
        prop_assume!(!v.has_loose_bvars());
        let result = e.instantiate(&v);
        prop_assert!(!result.has_loose_bvars(),
            "instantiate(closed_e, closed_v) should be closed");
    }
}

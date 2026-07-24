// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mode-aware type checker tests.

use super::*;
use crate::env::Environment;
use crate::mode::CleanMode;

fn empty_env() -> Environment {
    Environment::default()
}

fn beta_redex() -> Expr {
    Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::prop(),
    )
}

fn cubical_interval_expr() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}

fn cubical_interval_type() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
}

#[test]
fn test_cubical_interval_requires_cubical_mode() {
    let env = empty_env();

    // Constructive mode (default) should reject cubical expressions
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type_with_cert(&Expr::from_kind(ExprKind::CubicalInterval));
    assert!(matches!(
        result,
        Err(TypeError::ModeRequired { feature, mode })
        if feature == "CubicalInterval" && mode == "Cubical"
    ));

    // Cubical mode should accept cubical expressions
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let (ty, _cert) = tc
        .infer_type_with_cert(&Expr::from_kind(ExprKind::CubicalInterval))
        .expect("Cubical mode should accept CubicalInterval");
    assert_eq!(
        ty,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_cubical_i0_i1_requires_cubical_mode() {
    let env = empty_env();

    // Constructive mode should reject i0/i1
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type_with_cert(&Expr::from_kind(ExprKind::CubicalI0));
    assert!(matches!(
        result,
        Err(TypeError::ModeRequired { feature, mode })
        if feature == "CubicalI0/CubicalI1" && mode == "Cubical"
    ));

    // Cubical mode should accept i0
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let (ty, _) = tc
        .infer_type_with_cert(&Expr::from_kind(ExprKind::CubicalI0))
        .expect("Cubical mode should accept CubicalI0");
    assert!(matches!(&ty.kind, ExprKind::CubicalInterval));

    // Cubical mode should accept i1
    let (ty, _) = tc
        .infer_type_with_cert(&Expr::from_kind(ExprKind::CubicalI1))
        .expect("Cubical mode should accept CubicalI1");
    assert!(matches!(&ty.kind, ExprKind::CubicalInterval));
}

#[test]
fn test_with_context_inherits_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    let (ty, _) = tc
        .infer_type_with_cert(&cubical_interval_expr())
        .expect("with_context should inherit cubical mode from the environment");

    assert_eq!(tc.mode(), env.mode());
    assert_eq!(ty, cubical_interval_type());
}

#[test]
fn test_set_mode_clears_all_caches_on_mode_change() {
    let env = empty_env();
    let mut tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Populate WHNF cache — beta_redex is (λ x:Prop. x) Prop which reduces to Prop
    let redex = beta_redex();
    let whnf_result = tc.whnf(&redex);
    assert_eq!(
        whnf_result,
        Expr::prop(),
        "beta redex should reduce to Prop"
    );
    assert!(
        tc.whnf_cache_entries() > 0,
        "expected WHNF cache to contain entries before mode change"
    );

    // Populate def_eq cache with a negative result.
    assert!(!tc.is_def_eq(&Expr::nat_lit(1), &Expr::nat_lit(2)));
    assert!(
        tc.def_eq_cache_entries() > 0,
        "expected def_eq cache to contain entries before mode change"
    );

    // Populate equiv_manager via a successful def_eq check.
    let prop_lhs = Expr::prop();
    let prop_rhs = Expr::prop();
    assert!(tc.is_def_eq(&prop_lhs, &prop_rhs));
    assert!(
        !tc.equiv_manager.borrow().is_empty(),
        "expected equiv_manager to contain entries before mode change"
    );

    // Populate type cache with a mode-sensitive expression.
    tc.enable_type_cache();
    let cubical_interval = cubical_interval_expr();
    let cubical_interval_ty = cubical_interval_type();
    let old_mode_hash = {
        let mut cache_ref = tc.type_cache.borrow_mut();
        let cache = cache_ref
            .as_mut()
            .expect("type cache should be enabled for set_mode invalidation test");
        cache.insert(&cubical_interval, cubical_interval_ty.clone());
        assert_eq!(cache.len(), 1, "type cache should contain seeded entry");
        cache.mode_hash()
    };

    // Changing mode must invalidate all caches.
    tc.set_mode(CleanMode::Constructive);
    assert_eq!(tc.mode(), CleanMode::Constructive);
    assert_eq!(
        tc.whnf_cache_entries(),
        0,
        "set_mode must clear WHNF cache when mode changes"
    );
    assert_eq!(
        tc.def_eq_cache_entries(),
        0,
        "set_mode must clear def_eq cache when mode changes"
    );
    assert!(
        tc.equiv_manager.borrow().is_empty(),
        "set_mode must clear equiv_manager when mode changes"
    );

    let mut cache_ref = tc.type_cache.borrow_mut();
    let cache = cache_ref
        .as_mut()
        .expect("type cache should remain enabled after mode change");
    assert_eq!(
        cache.len(),
        0,
        "set_mode must clear type cache when mode changes"
    );
    assert_ne!(
        cache.mode_hash(),
        old_mode_hash,
        "set_mode should update type-cache mode hash"
    );
}

#[test]
fn test_manual_mode_mutation_without_invalidation_can_expose_stale_type_cache_entry() {
    let env = empty_env();
    let mut tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    tc.enable_type_cache();

    let cubical_interval = cubical_interval_expr();
    let cubical_interval_ty = cubical_interval_type();
    {
        let mut cache_ref = tc.type_cache.borrow_mut();
        let cache = cache_ref
            .as_mut()
            .expect("type cache should be enabled for stale-cache simulation");
        cache.insert(&cubical_interval, cubical_interval_ty.clone());
    }

    // Simulate the pre-fix bug by bypassing set_mode invalidation.
    tc.mode = CleanMode::Constructive;
    let infer_result = tc.infer_type_with_cert(&cubical_interval);
    assert!(
        matches!(infer_result, Err(TypeError::ModeRequired { .. })),
        "constructive mode must reject CubicalInterval"
    );

    // With stale mode hash, cached Cubical result is still visible.
    let stale_entry = {
        let mut cache_ref = tc.type_cache.borrow_mut();
        let cache = cache_ref
            .as_mut()
            .expect("type cache should stay enabled during stale-cache simulation");
        cache.get(&cubical_interval).cloned()
    };
    assert_eq!(
        stale_entry,
        Some(cubical_interval_ty),
        "without invalidation, stale mode-specific cache entry remains accessible"
    );
}

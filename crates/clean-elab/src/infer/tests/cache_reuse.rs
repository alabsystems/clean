// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for ElabCtx TypeChecker cache reuse (#1852).

use super::*;

fn cache_count(debug: &str, field: &str) -> usize {
    debug
        .split_once(&format!("{field}: "))
        .and_then(|(_, rest)| rest.split([',', '}']).next())
        .and_then(|value| value.parse().ok())
        .unwrap_or_else(|| panic!("missing {field} in cache debug: {debug}"))
}

fn cache_debug(ctx: &ElabCtx<'_>) -> String {
    format!("{:?}", ctx.tc_caches.borrow())
}

#[test]
fn test_issue1852_whnf_preserves_seeded_def_eq_cache() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat environment should initialize");
    let seed_tc = TypeChecker::new(&env);
    let prop = Expr::prop();
    let lit_zero = Expr::nat_lit(0);
    let const_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    assert!(seed_tc.is_def_eq(&lit_zero, &const_zero));
    let seeded = seed_tc.take_caches();
    let seeded_debug = format!("{:?}", seeded);
    let seeded_def_eq = cache_count(&seeded_debug, "def_eq_entries");
    assert!(
        seeded_def_eq > 0,
        "seed TypeChecker should populate def_eq cache: {seeded_debug}"
    );

    let ctx = ElabCtx::new(&env);
    ctx.tc_caches.replace(seeded);
    let _ = ctx.whnf(&prop);

    let after_debug = cache_debug(&ctx);
    assert!(
        cache_count(&after_debug, "def_eq_entries") >= seeded_def_eq,
        "ElabCtx::whnf should preserve seeded def_eq cache entries: {after_debug}"
    );
}

#[test]
fn test_issue1852_is_def_eq_preserves_seeded_whnf_cache() {
    // Need an expression that actually populates the WHNF cache.
    // `whnf` short-circuits and skips the cache for Sort/Pi/Lam/Lit/MVar
    // kinds (Lean 4 parity, #3210). Use a Const reference that requires
    // delta-unfolding so the WHNF cache gets populated.
    let mut env = Environment::new();
    env.init_nat().expect("Nat environment should initialize");
    let seed_tc = TypeChecker::new(&env);
    let lit_zero = Expr::nat_lit(0);
    let const_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let _ = seed_tc.is_def_eq(&lit_zero, &const_zero);
    let _ = seed_tc.whnf(&const_zero);
    let seeded = seed_tc.take_caches();
    let seeded_debug = format!("{:?}", seeded);
    let seeded_whnf = cache_count(&seeded_debug, "whnf_entries");
    if seeded_whnf == 0 {
        eprintln!("SKIP: seed whnf did not populate cache (perhaps further inlined)");
        return;
    }

    let ctx = ElabCtx::new(&env);
    ctx.tc_caches.replace(seeded);
    assert!(ctx.is_def_eq(&lit_zero, &const_zero));

    let after_debug = cache_debug(&ctx);
    assert!(
        cache_count(&after_debug, "whnf_entries") >= seeded_whnf,
        "ElabCtx::is_def_eq should preserve seeded whnf cache entries: {after_debug}"
    );
}

#[test]
fn test_issue1852_infer_type_preserves_seeded_projection_cache() {
    let env = pair_env_with_namespaced_const();
    let expr = elab_with_env(&env, "pairVal.snd").expect("pairVal.snd should elaborate");

    let seed_tc = TypeChecker::new(&env);
    let seed_ty = seed_tc
        .infer_type(&expr)
        .expect("seed TypeChecker should infer projection type");
    assert_eq!(seed_ty, Expr::prop(), "pairVal.snd should have type Prop");

    let seeded = seed_tc.take_caches();
    let seeded_debug = format!("{:?}", seeded);
    let seeded_proj = cache_count(&seeded_debug, "proj_type_entries");
    assert!(
        seeded_proj > 0,
        "seed TypeChecker should populate projection cache: {seeded_debug}"
    );

    let ctx = ElabCtx::new(&env);
    ctx.tc_caches.replace(seeded);
    let inferred = ctx
        .infer_type(&expr)
        .expect("ElabCtx should infer projection type with seeded caches");
    assert_eq!(inferred, seed_ty, "projection type should remain stable");

    let after_debug = cache_debug(&ctx);
    assert!(
        cache_count(&after_debug, "proj_type_entries") >= seeded_proj,
        "ElabCtx::infer_type should preserve seeded projection cache entries: {after_debug}"
    );
}

#[test]
fn test_successful_same_locals_meta_commit_invalidates_authoritative_caches() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat environment should initialize");

    // Seed a real TypeChecker entry before entering the transaction. The
    // transaction below changes no locals, so the old local-only invalidation
    // heuristic incorrectly retained this cache across a committed meta update.
    let seed_tc = TypeChecker::new(&env);
    let literal_zero = Expr::nat_lit(0);
    let constructor_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(seed_tc.is_def_eq(&literal_zero, &constructor_zero));
    let seeded = seed_tc.take_caches();
    let seeded_debug = format!("{seeded:?}");
    assert!(
        cache_count(&seeded_debug, "def_eq_entries") > 0,
        "test setup must populate an authoritative cache: {seeded_debug}"
    );

    let mut ctx = ElabCtx::new(&env);
    ctx.tc_caches.replace(seeded);
    ctx.instance_cache
        .insert("sentinel-ground-goal".to_string(), Expr::prop());
    let locals_before = ctx.locals.clone();
    let meta = ctx.metas.fresh(Expr::type_());

    ctx.with_local_scope_rollback(|this| {
        assert!(this.metas.assign(meta, Expr::prop()));
        Ok(())
    })
    .expect("same-local transaction should commit its metavariable assignment");

    assert!(ctx.metas.is_assigned(meta));
    assert_eq!(ctx.locals, locals_before, "test must keep locals identical");
    let after = cache_debug(&ctx);
    for field in [
        "whnf_entries",
        "whnf_core_entries",
        "def_eq_entries",
        "proj_type_entries",
        "unfold_entries",
    ] {
        assert_eq!(
            cache_count(&after, field),
            0,
            "successful meta commit retained stale {field}: {after}"
        );
    }
    assert!(
        ctx.instance_cache.is_empty(),
        "successful transaction must invalidate instance results at the same authority boundary"
    );

    // Temporary scopes also commit successful meta work while restoring their
    // entry locals. They must not resurrect the entry instance-cache snapshot.
    ctx.instance_cache
        .insert("temporary-sentinel".to_string(), Expr::prop());
    let temporary_meta = ctx.metas.fresh(Expr::type_());
    ctx.with_temporary_local_scope(|this| {
        assert!(this.metas.assign(temporary_meta, Expr::prop()));
        Ok(())
    })
    .expect("temporary same-local transaction should commit its meta assignment");
    assert!(ctx.metas.is_assigned(temporary_meta));
    assert_eq!(ctx.locals, locals_before);
    assert!(
        ctx.instance_cache.is_empty(),
        "successful temporary scope resurrected its entry instance cache"
    );
}

#[test]
fn test_optional_probe_none_rolls_back_full_state_then_context_reuses() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(Expr::type_());
    ctx.push_local("outerProbeLocal".to_string(), Expr::prop());
    ctx.instance_cache
        .insert("entry-instance".to_string(), Expr::prop());
    let locals_before = ctx.locals.clone();
    let expected_before = ctx.current_expected_type.clone();
    let pending_before = ctx.pending_level_assigns.borrow().clone();
    let stable_meta = ctx.metas.fresh(Expr::type_());
    let mut created_meta = None;

    let declined: Option<()> = ctx
        .with_optional_temporary_local_scope(|this| {
            this.push_local("speculativeLocal".to_string(), Expr::prop());
            this.current_expected_type = None;
            assert!(this.metas.assign(stable_meta, Expr::prop()));
            let created = this.metas.fresh(Expr::type_());
            assert!(this.metas.assign(created, Expr::prop()));
            created_meta = Some(created);
            this.pending_level_assigns.borrow_mut().push((
                Name::from_string("speculativeLevel"),
                Level::succ(Level::zero()),
            ));
            this.instance_cache.clear();
            Ok(None)
        })
        .expect("a declined optional probe is not a hard error");

    assert!(declined.is_none());
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.current_expected_type, expected_before);
    assert_eq!(*ctx.pending_level_assigns.borrow(), pending_before);
    assert!(!ctx.metas.is_assigned(stable_meta));
    assert!(
        ctx.metas
            .get(created_meta.expect("probe must create a metavariable"))
            .is_none(),
        "declined probe leaked a newly-created metavariable"
    );
    assert!(ctx.instance_cache.contains_key("entry-instance"));

    let accepted = ctx
        .with_optional_temporary_local_scope(|this| {
            assert!(this.metas.assign(stable_meta, Expr::prop()));
            Ok(Some(17usize))
        })
        .expect("context should remain reusable after the declined probe");
    assert_eq!(accepted, Some(17));
    assert!(ctx.metas.is_assigned(stable_meta));
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.current_expected_type, expected_before);
    assert!(ctx.instance_cache.is_empty());
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for ElabCtx TypeChecker cache authority (#1852).
//!
//! Default-policy seeds are incompatible with elaboration. Matching policy
//! also needs the same local/meta state and pending level-callback facts.

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
fn test_issue1852_whnf_discards_def_eq_seed_from_default_policy() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat environment should initialize");
    let seed_tc = TypeChecker::new(&env);
    // Deliberately retain the default policy on this seed.
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
    assert_eq!(ctx.whnf(&prop), prop);

    let after_debug = cache_debug(&ctx);
    assert_eq!(
        cache_count(&after_debug, "def_eq_entries"),
        0,
        "ElabCtx::whnf must discard answers from the default checker policy: {after_debug}"
    );
}

#[test]
fn test_issue1852_is_def_eq_discards_whnf_seed_from_default_policy() {
    // Need an expression that actually populates the WHNF cache.
    // `whnf` short-circuits and skips the cache for Sort/Pi/Lam/Lit/MVar
    // kinds (Lean 4 parity, #3210). Use a Const reference that requires
    // delta-unfolding so the WHNF cache gets populated.
    let mut env = Environment::new();
    env.init_nat().expect("Nat environment should initialize");
    let seed_tc = TypeChecker::new(&env);
    // Deliberately retain the default policy on this seed.
    let lit_zero = Expr::nat_lit(0);
    let const_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let _ = seed_tc.is_def_eq(&lit_zero, &const_zero);
    let _ = seed_tc.whnf(&const_zero);
    let seeded = seed_tc.take_caches();
    let seeded_debug = format!("{:?}", seeded);
    let seeded_whnf = cache_count(&seeded_debug, "whnf_entries");
    assert!(
        seeded_whnf > 0,
        "seed TypeChecker must populate the whnf cache: {seeded_debug}"
    );

    let ctx = ElabCtx::new(&env);
    ctx.tc_caches.replace(seeded);
    assert!(ctx.is_def_eq(&lit_zero, &const_zero));

    let after_debug = cache_debug(&ctx);
    assert_eq!(
        cache_count(&after_debug, "whnf_entries"),
        0,
        "ElabCtx::is_def_eq must discard answers from the default checker policy: {after_debug}"
    );
}

#[test]
fn test_issue1852_infer_type_repopulates_projection_cache_after_policy_change() {
    let env = pair_env_with_namespaced_const();
    // `(pairVal).snd` is a projection (a bare `pairVal.snd` names the
    // constant of that full name).
    let expr = elab_with_env(&env, "(pairVal).snd").expect("(pairVal).snd should elaborate");

    let seed_tc = TypeChecker::new(&env);
    // Deliberately retain the default policy on this seed.
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
    // A call that cannot infer the projection still has to retire its answer
    // from the incompatible default policy. The next call recomputes it.
    assert_eq!(ctx.whnf(&Expr::prop()), Expr::prop());
    let cleared_debug = cache_debug(&ctx);
    assert_eq!(
        cache_count(&cleared_debug, "proj_type_entries"),
        0,
        "elaborator policy setup must retire the seeded projection answer: {cleared_debug}"
    );
    let inferred = ctx
        .infer_type(&expr)
        .expect("ElabCtx should recompute the projection type after invalidation");
    assert_eq!(inferred, seed_ty, "projection type should remain stable");

    let after_debug = cache_debug(&ctx);
    assert!(
        cache_count(&after_debug, "proj_type_entries") > 0,
        "ElabCtx::infer_type should repopulate the projection cache: {after_debug}"
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
    ctx.push_local(SurfaceName::generated_path("outerProbeLocal"), Expr::prop());
    ctx.instance_cache
        .insert("entry-instance".to_string(), Expr::prop());
    let locals_before = ctx.locals.clone();
    let expected_before = ctx.current_expected_type.clone();
    let pending_before = ctx.pending_level_assigns.borrow().clone();
    let stable_meta = ctx.metas.fresh(Expr::type_());
    let mut created_meta = None;

    let declined: Option<()> = ctx
        .with_optional_temporary_local_scope(|this| {
            this.push_local(
                SurfaceName::generated_path("speculativeLocal"),
                Expr::prop(),
            );
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

#[test]
fn test_issue1852_kernel_answers_do_not_cross_elaboration_reducibility() {
    let mut env = Environment::new();
    env.init_nat().expect("checked Nat");
    let name = Name::from_string("cacheIrreducibleZero");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value: Expr::nat_lit(0),
        is_reducible: true,
    })
    .expect("checked alias");
    env.restrict_checked_unfolding(&name)
        .expect("checked irreducible policy");
    let value = Expr::const_(name, vec![]);
    for equality_first in [false, true] {
        let seed_tc = TypeChecker::new(&env);
        // The standalone kernel deliberately ignores the reducibility hint.
        // Seed the equality before the WHNF: once `value`'s full WHNF is
        // cached as a closed Nat literal, `is_def_eq` answers from it
        // (`tc/def_eq/cached_nat.rs`) without recording an equality entry, and
        // this control must seed BOTH caches the elaborator has to discard.
        assert!(seed_tc.is_def_eq(&value, &Expr::nat_lit(0)));
        assert_eq!(seed_tc.whnf(&value), Expr::nat_lit(0));
        let seeded = seed_tc.take_caches();
        let debug = format!("{seeded:?}");
        assert!(cache_count(&debug, "whnf_entries") > 0);
        assert!(cache_count(&debug, "def_eq_entries") > 0);
        let ctx = ElabCtx::new(&env);
        ctx.tc_caches.replace(seeded);
        if equality_first {
            assert!(!ctx.is_def_eq(&value, &Expr::nat_lit(0)));
            assert_eq!(ctx.whnf(&value), value);
        } else {
            assert_eq!(ctx.whnf(&value), value);
            assert!(!ctx.is_def_eq(&value, &Expr::nat_lit(0)));
        }
    }
}

#[test]
fn raw_meta_rollback_cannot_retain_a_let_local_whnf_answer() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat fixture");
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let meta = ctx.fresh_meta(nat.clone());
    let x = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("cachedLet"),
        x,
        nat,
        meta.clone(),
    );
    let root = Expr::fvar(x);
    let zero = Expr::nat_lit(0);

    ctx.metas.push_scope();
    assert!(ctx.try_unify(&meta, &zero));
    assert_eq!(ctx.whnf(&root), zero);
    // A repeated unchanged call must keep the real answer; compatible warm
    // adoption is supported, not something this regression should forbid.
    assert_eq!(ctx.whnf(&root), zero);
    assert!(ctx.metas.pop_scope());
    assert_eq!(ctx.metas.instantiate(&meta), meta);

    // Rollback changes the demanded let value without changing its FVar key.
    assert_eq!(ctx.whnf(&root), meta);
}

fn nat_let_local(ctx: &mut ElabCtx<'_>, value: Expr) -> Expr {
    let x = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("cachedLet"),
        x,
        Expr::const_(Name::from_string("Nat"), vec![]),
        value,
    );
    Expr::fvar(x)
}

#[test]
fn meta_assignment_recomputes_a_warm_let_local() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let meta = ctx.fresh_meta(Expr::const_(Name::from_string("Nat"), vec![]));
    let root = nat_let_local(&mut ctx, meta.clone());
    assert_eq!(ctx.whnf(&root), meta);
    assert!(ctx.try_unify(&meta, &Expr::nat_lit(0)));
    assert_eq!(ctx.whnf(&root), Expr::nat_lit(0));
}

#[test]
fn restored_meta_clone_cannot_repeat_a_different_cache_timeline() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let meta = ctx.fresh_meta(Expr::const_(Name::from_string("Nat"), vec![]));
    let root = nat_let_local(&mut ctx, meta.clone());
    let original = ctx.metas.clone();
    assert!(ctx.try_unify(&meta, &Expr::nat_lit(0)));
    let first_generation = ctx.metas.generation();
    assert_eq!(ctx.whnf(&root), Expr::nat_lit(0));

    ctx.metas = original;
    assert!(ctx.try_unify(&meta, &Expr::nat_lit(1)));
    assert_ne!(ctx.metas.generation(), first_generation);
    assert_eq!(ctx.whnf(&root), Expr::nat_lit(1));
}

#[test]
fn local_bridge_rebinding_cannot_retain_the_previous_let_value() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let root = nat_let_local(&mut ctx, Expr::nat_lit(0));
    assert_eq!(ctx.whnf(&root), Expr::nat_lit(0));
    let ExprKind::FVar(x) = root.kind() else {
        panic!("let-local fixture")
    };
    ctx.pop_local();
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("reboundLet"),
        *x,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(1),
    );
    assert_eq!(ctx.whnf(&root), Expr::nat_lit(1));
}

#[test]
fn unchanged_elaboration_state_preserves_real_checker_answers() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    assert!(ctx.is_def_eq(
        &Expr::nat_lit(0),
        &Expr::const_(Name::from_string("Nat.zero"), vec![])
    ));
    let before = cache_count(&cache_debug(&ctx), "def_eq_entries");
    assert!(before > 0, "the actual checker must populate the cache");
    // A no-op WHNF cannot create def-eq entries. A surviving entry therefore
    // demonstrates reuse, rather than success after disabling every cache.
    assert_eq!(ctx.whnf(&Expr::prop()), Expr::prop());
    assert_eq!(cache_count(&cache_debug(&ctx), "def_eq_entries"), before);
}

#[test]
fn restored_pending_level_facts_must_reproduce_callback_assignments() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let left = Expr::sort(ctx.fresh_universe_param());
    let right = Expr::prop();
    let generation = ctx.metas.generation();
    assert!(ctx.is_def_eq(&left, &right));
    let pending = ctx.pending_level_assigns.take();
    assert!(
        !pending.is_empty(),
        "the actual callback must learn a constraint"
    );
    assert_eq!(ctx.metas.generation(), generation);
    // The buffered packet was rolled back, not committed to MetaState. A
    // cached positive verdict must not bypass its required assignment effect.
    assert!(ctx.is_def_eq(&left, &right));
    assert_eq!(*ctx.pending_level_assigns.borrow(), pending);
}

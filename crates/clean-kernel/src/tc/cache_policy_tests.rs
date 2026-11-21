// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::Declaration;

fn environment(irreducible: bool) -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("checked Nat");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("cachePolicyZero"),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value: Expr::nat_lit(0),
        is_reducible: true,
    })
    .expect("checked alias");
    if irreducible {
        env.restrict_checked_unfolding(&Name::from_string("cachePolicyZero"))
            .expect("checked restrictive policy");
    }
    env
}
fn alias() -> Expr {
    Expr::const_str("cachePolicyZero")
}
fn seed(tc: &TypeChecker<'_>) -> TcCaches {
    assert!(tc.is_def_eq(&alias(), &Expr::nat_lit(0)));
    assert_eq!(tc.whnf(&alias()), Expr::nat_lit(0));
    let caches = tc.take_caches();
    assert!(!caches.whnf.is_empty(), "real WHNF answers required");
    assert!(!caches.def_eq.is_empty(), "real equality answers required");
    caches
}
fn assert_empty(caches: &TcCaches) {
    assert!(caches.whnf.is_empty());
    assert!(caches.whnf_core.is_empty());
    assert!(caches.def_eq.is_empty());
    assert!(caches.proj_type.is_empty());
    assert!(caches.unfold.is_empty());
    assert!(caches.equiv.is_empty());
}

fn adopt_profile_cache(
    env: &Environment,
    mode: CleanMode,
    path: usize,
    caches: TcCaches,
) -> TypeChecker<'_> {
    match path {
        0 => TypeChecker::with_context_and_caches(env, LocalContext::new(), caches),
        1 => TypeChecker::with_mode_and_caches(env, mode, caches),
        2 => TypeChecker::new(env).with_configured_caches(caches),
        _ => panic!("finite cache adoption paths"),
    }
}

#[test]
fn source_world_profile_handoffs_discard_incompatible_answers_before_export() {
    use crate::level::LeanLevelProfile;
    for from_profile in [LeanLevelProfile::Lean430, LeanLevelProfile::Lean48] {
        let mut from = environment(false);
        from.set_kernel_theory(crate::env::KernelTheory::Lean);
        from.set_lean_level_profile(from_profile);
        let mut to = from.clone();
        to.set_lean_level_profile(if from_profile == LeanLevelProfile::Lean430 {
            LeanLevelProfile::Lean48
        } else {
            LeanLevelProfile::Lean430
        });
        for path in 0..3 {
            let tc = TypeChecker::new(&from);
            let caches = seed(&tc);
            let replay = adopt_profile_cache(&to, tc.mode, path, caches);
            // No semantic query or setter may conceal a missing profile fence.
            assert_empty(&replay.take_caches());
        }
    }
}

#[test]
fn matching_source_world_profile_handoffs_preserve_real_answers() {
    use crate::level::LeanLevelProfile;
    for profile in [LeanLevelProfile::Lean430, LeanLevelProfile::Lean48] {
        let mut env = environment(false);
        env.set_kernel_theory(crate::env::KernelTheory::Lean);
        env.set_lean_level_profile(profile);
        for path in 0..3 {
            let tc = TypeChecker::new(&env);
            let caches = seed(&tc);
            let before = (caches.whnf.len(), caches.def_eq.len());
            let replay = adopt_profile_cache(&env, tc.mode, path, caches);
            let after = replay.take_caches();
            assert!(after.whnf.len() >= before.0);
            assert!(after.def_eq.len() >= before.1);
        }
    }
}

#[test]
fn configured_adoption_cannot_transfer_a_modern_positive_level_verdict() {
    use crate::level::LeanLevelProfile;
    let mut modern = environment(false);
    modern.set_kernel_theory(crate::env::KernelTheory::Lean);
    modern.set_lean_level_profile(LeanLevelProfile::Lean430);
    let mut legacy = modern.clone();
    legacy.set_lean_level_profile(LeanLevelProfile::Lean48);
    let left = Expr::sort(Level::lean_imax_core(
        Level::succ(Level::zero()),
        Level::param(Name::from_string("u")),
    ));
    let right = Expr::sort(Level::param(Name::from_string("u")));
    for path in 0..3 {
        let tc = TypeChecker::new(&modern);
        assert!(tc.is_def_eq(&left, &right));
        let caches = tc.take_caches();
        assert!(!caches.def_eq.is_empty(), "real positive verdict required");
        let replay = adopt_profile_cache(&legacy, tc.mode, path, caches);
        // No setter runs after adoption: this checks the handoff's own fence.
        assert!(!replay.is_def_eq(&left, &right));
    }
}
fn configure(tc: &mut TypeChecker<'_>) {
    tc.set_kernel_theory(crate::env::KernelTheory::LeanReference);
    tc.set_mode(CleanMode::Classical);
    tc.set_honor_reducibility(true);
    tc.set_transparency(TransparencyMode::All);
    tc.set_cumulative(true);
    tc.set_level_params(vec![Name::from_string("u")]);
}

#[test]
fn matching_default_handoff_preserves_answers_and_defaults() {
    let env = environment(false);
    let tc = TypeChecker::new(&env);
    let caches = seed(&tc);
    let before = (caches.whnf.len(), caches.def_eq.len());
    let replay = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches);
    assert!(!replay.honors_reducibility());
    assert_eq!(replay.transparency(), TransparencyMode::Default);
    assert_eq!(replay.whnf(&Expr::prop()), Expr::prop());
    let caches = replay.take_caches();
    assert!(caches.whnf.len() >= before.0);
    assert!(caches.def_eq.len() >= before.1);
}

#[test]
fn configure_before_adoption_preserves_matching_nondefault_answers() {
    let env = environment(false);
    let mut tc = TypeChecker::new(&env);
    configure(&mut tc);
    let caches = seed(&tc);
    let before = (caches.whnf.len(), caches.def_eq.len());
    let mut replay =
        TypeChecker::with_context_and_caches(&env, LocalContext::new(), TcCaches::default());
    // Installing a compatible callback before adoption must not discard the
    // saved answers. Live callback changes remain invalidating below.
    replay.set_level_eq_override(|a, b| a == b);
    configure(&mut replay);
    let replay = replay.with_configured_caches(caches);
    let caches = replay.take_caches();
    assert!(caches.whnf.len() >= before.0);
    assert!(caches.def_eq.len() >= before.1);
}

#[test]
fn untouched_import_export_cannot_relabel_incompatible_policies() {
    let env = environment(false);
    for changed in 0..8 {
        let mut tc = TypeChecker::new(&env);
        match changed {
            0 => tc.set_honor_reducibility(true),
            1 => tc.set_transparency(TransparencyMode::All),
            2 => tc.set_mode(CleanMode::Classical),
            3 => tc.set_allow_unsafe(false),
            4 => tc.set_allow_partial(false),
            5 => tc.set_cumulative(true),
            6 => tc.set_level_params(vec![Name::from_string("u")]),
            7 => tc.set_kernel_theory(crate::env::KernelTheory::LeanReference),
            _ => unreachable!("finite test cases"),
        }
        let caches = seed(&tc);
        let replay = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches);
        // No semantic query occurred between import and export.
        assert_empty(&replay.take_caches());
    }
}

#[test]
fn honor_and_transparency_changes_cannot_reuse_irreducible_answers() {
    let env = environment(true);
    for from_all in [false, true] {
        for equality_first in [false, true] {
            let mut tc = TypeChecker::new(&env);
            if from_all {
                tc.set_honor_reducibility(true);
                tc.set_transparency(TransparencyMode::All);
            }
            let caches = seed(&tc);
            let replay = TypeChecker::with_context_and_caches(
                &env,
                LocalContext::new(),
                TcCaches::default(),
            );
            replay.set_honor_reducibility(true);
            let replay = replay.with_configured_caches(caches);
            if equality_first {
                assert!(!replay.is_def_eq(&alias(), &Expr::nat_lit(0)));
                assert_eq!(replay.whnf(&alias()), alias());
            } else {
                assert_eq!(replay.whnf(&alias()), alias());
                assert!(!replay.is_def_eq(&alias(), &Expr::nat_lit(0)));
            }
        }
    }
}

#[test]
fn callback_and_universe_scope_changes_still_discard_live_answers() {
    let env = environment(false);
    for callback in [false, true] {
        let tc = TypeChecker::new(&env);
        let caches = seed(&tc);
        let mut replay = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches);
        if callback {
            replay.set_level_eq_override(|a, b| a == b);
        } else {
            replay.set_level_params(vec![Name::from_string("other")]);
        }
        assert_empty(&replay.take_caches());
    }
}

#[test]
fn every_empty_constructor_and_adoption_establishes_actual_policy() {
    let env = environment(false);
    let checkers = [
        TypeChecker::new(&env),
        TypeChecker::with_mode(&env, CleanMode::Classical),
        TypeChecker::with_context(&env, LocalContext::new()),
        TypeChecker::with_context_and_mode(&env, LocalContext::new(), CleanMode::Classical),
        TypeChecker::with_transparency(&env, TransparencyMode::All),
        TypeChecker::with_context_and_caches(&env, LocalContext::new(), TcCaches::default()),
        TypeChecker::with_mode_and_caches(&env, CleanMode::Classical, TcCaches::default()),
        TypeChecker::new(&env).with_configured_caches(TcCaches::default()),
    ];
    for checker in checkers {
        assert_eq!(
            *checker.cached_policy.borrow(),
            Some(cache_policy::CachePolicy::capture(&checker))
        );
    }
}

#[test]
fn empty_import_preserves_every_existing_policy_owner_before_use() {
    let env = environment(false);
    for path in 0..3 {
        let tc = TypeChecker::new(&env);
        tc.set_honor_reducibility(true);
        let caches = tc.take_caches();
        assert_empty(&caches);
        let owner = caches.policy.clone();
        let replay = match path {
            0 => TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches),
            1 => TypeChecker::with_mode_and_caches(&env, CleanMode::Classical, caches),
            _ => TypeChecker::new(&env).with_configured_caches(caches),
        };
        assert_eq!(*replay.cached_policy.borrow(), owner);
        assert_ne!(
            *replay.cached_policy.borrow(),
            Some(cache_policy::CachePolicy::capture(&replay))
        );
        let exported = replay.take_caches();
        assert_empty(&exported);
        assert_eq!(
            exported.policy,
            Some(cache_policy::CachePolicy::capture(&replay))
        );
    }
}

#[test]
fn unowned_nonempty_retained_containers_are_never_promoted() {
    let env = environment(false);
    for retained in 0..7 {
        for path in 0..3 {
            let tc = TypeChecker::new(&env);
            // Establish real semantic answers before isolating one retained
            // container. Unknown ownership must also reject an arbitrary
            // projection-cache payload without reading it as an answer.
            let mut caches = seed(&tc);
            caches.policy = None;
            caches.whnf.clear();
            caches.whnf_core.clear();
            caches.def_eq.clear();
            caches.proj_type.clear();
            caches.unfold.clear();
            caches.equiv.clear();
            match retained {
                0 => caches.whnf.insert(alias(), Expr::nat_lit(0)),
                1 => caches.whnf_core.insert(alias(), Expr::nat_lit(0)),
                2 => caches.def_eq.insert(
                    DefEqCacheKey::new(&alias(), &Expr::nat_lit(0), tc.transparency()),
                    true,
                ),
                3 => caches.proj_type.insert(alias(), Expr::const_str("Nat")),
                4 => caches.unfold.insert(alias(), Expr::nat_lit(0)),
                _ => {
                    caches.equiv.add_equiv(&alias(), &Expr::nat_lit(0));
                    if retained == 6 {
                        assert!(caches.equiv.trim_if_needed(0));
                    }
                }
            }
            assert!(
                !caches.whnf.is_empty()
                    || !caches.whnf_core.is_empty()
                    || !caches.def_eq.is_empty()
                    || !caches.proj_type.is_empty()
                    || !caches.unfold.is_empty()
                    || !caches.equiv.is_empty()
            );
            let replay = match path {
                0 => TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches),
                1 => TypeChecker::with_mode_and_caches(&env, env.mode(), caches),
                _ => TypeChecker::new(&env).with_configured_caches(caches),
            };
            assert!(replay.cached_policy.borrow().is_none());
            assert_empty(&replay.take_caches());
        }
    }
}

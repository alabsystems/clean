// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Measurement tests for the simp performance brick (2026-08-11):
//!
//! 1. the per-environment [`collect_simp_lemmas_cached`] cache — a second simp
//!    collection against an unchanged environment must REUSE the built
//!    `SimpLemmaSet` instead of re-parsing ~10k lemma types and re-inserting
//!    them into the discrimination tree, and any environment mutation must
//!    conservatively rebuild;
//! 2. the head-const fast path in `SimpLemmaSet::candidates` — a
//!    `Const`-headed goal subterm must consult strictly fewer lemmas than the
//!    full set, while star-bucketed lemmas stay reachable at their own head.

use std::sync::Arc;

use clean_kernel::env::{Declaration, SimpPriority};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};

use crate::tactic::simp::{cacheable_rebuild_count, collect_simp_lemmas_cached, SimpConfig};
use crate::tactic::ProofState;

/// `@Eq.{1} Nat lhs rhs`.
fn mk_eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// `@Eq.{1} Prop lhs rhs`.
fn mk_eq_prop(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::prop(),
            ),
            lhs,
        ),
        rhs,
    )
}

fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn perf_const_name(salt: &str, i: usize) -> Name {
    Name::from_string(&format!("SimpPerf.{salt}.c{i}"))
}

fn perf_lemma_name(salt: &str, i: usize) -> Name {
    Name::from_string(&format!("SimpPerf.{salt}.lem{i}"))
}

/// Environment with `lemma_count` registered `@[simp]`-style equality lemmas
/// (`SimpPerf.lem{i} : SimpPerf.c{i} = Nat.zero`, each tree-indexable under its
/// own head constant), plus:
/// - `SimpPerf.eq_zz_refl` — a SPECIFIC Eq-rooted lemma
///   (`(Nat.zero = Nat.zero) = (Nat.zero = Nat.zero)`), which the
///   discrimination tree accepts;
/// - `SimpPerf.eq_flip` — the trivially-generic `Eq ?α ?a ?b` shape
///   (`∀ α a b, (a = b) = (b = a)`), which `insert_if_specific` REFUSES, so it
///   lands in the unindexed head-const bucket under `Eq`.
///
/// The `salt` keeps each test's declarations (and therefore its cache key
/// fingerprint) distinct, so tests stay isolated even if a single-threaded
/// test run shares one thread-local cache.
fn build_env(salt: &str, lemma_count: usize) -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init nat");
    env.init_eq().expect("init eq");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for i in 0..lemma_count {
        let c_name = perf_const_name(salt, i);
        env.add_decl(Declaration::Axiom {
            name: c_name.clone(),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("register head constant");
        let lem_name = perf_lemma_name(salt, i);
        env.add_decl(Declaration::Axiom {
            name: lem_name.clone(),
            level_params: vec![],
            type_: mk_eq_nat(Expr::const_(c_name, vec![]), nat_zero()),
        })
        .expect("register equality lemma");
        env.register_simp_lemma(lem_name, SimpPriority::Default);
    }

    // Tree-indexed Eq-rooted lemma: specific arguments keep it keyable.
    let eq_zz = mk_eq_nat(nat_zero(), nat_zero());
    let zz_name = Name::from_string("SimpPerf.eq_zz_refl");
    env.add_decl(Declaration::Axiom {
        name: zz_name.clone(),
        level_params: vec![],
        type_: mk_eq_prop(eq_zz.clone(), eq_zz),
    })
    .expect("register specific Eq-rooted lemma");
    env.register_simp_lemma(zz_name, SimpPriority::Default);

    // Refused Eq-star lemma: `∀ (α : Sort 1) (a b : α), (a = b) = (b = a)`.
    // Its LHS keys as [Const(Eq,3), Star, Star, Star] — the trivially-generic
    // shape the tree refuses — so it must land in the `Eq` head bucket.
    let eq_generic = |a: u32, b: u32| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    Expr::bvar(2),
                ),
                Expr::bvar(a),
            ),
            Expr::bvar(b),
        )
    };
    let flip_type = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::succ(Level::zero())),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                mk_eq_prop(eq_generic(1, 0), eq_generic(0, 1)),
            ),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("SimpPerf.eq_flip"),
        level_params: vec![],
        type_: flip_type,
    })
    .expect("register generic Eq-star lemma");
    env.register_simp_lemma(Name::from_string("SimpPerf.eq_flip"), SimpPriority::Default);

    env
}

fn state_for(env: Environment) -> ProofState {
    ProofState::new(env, mk_eq_nat(nat_zero(), nat_zero()))
}

#[test]
fn test_simp_cache_second_call_reuses_built_set() {
    let state = state_for(build_env("reuse", 1000));
    let config = SimpConfig::new();

    let before = cacheable_rebuild_count();
    let first = collect_simp_lemmas_cached(&state, &config);
    let second = collect_simp_lemmas_cached(&state, &config);

    assert!(
        first.len() >= 1000,
        "the ~1000 registered registry lemmas should all be collected, got {}",
        first.len()
    );
    assert_eq!(
        cacheable_rebuild_count(),
        before + 1,
        "second collection against an unchanged environment must reuse the cache"
    );
    assert!(
        Arc::ptr_eq(&first, &second),
        "cache hit must return the identical built set, not a copy"
    );
}

#[test]
fn test_simp_cache_rebuilds_when_registry_gains_a_lemma() {
    let env = build_env("grow", 50);
    let config = SimpConfig::new();

    let state = state_for(env.clone());
    let before = cacheable_rebuild_count();
    let first = collect_simp_lemmas_cached(&state, &config);

    // A declaration registering between tactic calls must invalidate.
    let mut grown = env;
    grown
        .add_decl(Declaration::Axiom {
            name: Name::from_string("SimpPerf.late"),
            level_params: vec![],
            type_: mk_eq_nat(nat_zero(), nat_zero()),
        })
        .expect("register late lemma declaration");
    grown.register_simp_lemma(Name::from_string("SimpPerf.late"), SimpPriority::Default);
    let grown_state = state_for(grown);
    let second = collect_simp_lemmas_cached(&grown_state, &config);

    assert_eq!(
        cacheable_rebuild_count(),
        before + 2,
        "a grown simp registry must force a rebuild"
    );
    let late = Name::from_string("SimpPerf.late");
    assert!(
        second.iter().any(|l| l.name == late),
        "the freshly registered lemma must be in the rebuilt set"
    );
    assert_eq!(second.len(), first.len() + 1);
}

#[test]
fn test_simp_cache_conservative_on_unregister_reregister() {
    let env = build_env("churn", 50);
    let config = SimpConfig::new();

    let state = state_for(env.clone());
    let before = cacheable_rebuild_count();
    let _ = collect_simp_lemmas_cached(&state, &config);

    // Remove + re-add leaves count AND content fingerprint identical, but the
    // simp-registry revision still differs: the cache must rebuild, never
    // assume.
    let mut churned = env;
    assert!(churned.unregister_simp_lemma(&perf_lemma_name("churn", 0)));
    churned.register_simp_lemma(perf_lemma_name("churn", 0), SimpPriority::Default);
    let churned_state = state_for(churned);
    let _ = collect_simp_lemmas_cached(&churned_state, &config);

    assert_eq!(
        cacheable_rebuild_count(),
        before + 2,
        "an unregister/re-register cycle bumps the simp-registry revision and must rebuild"
    );
}

#[test]
fn test_simp_cache_bypasses_goal_dependent_configs() {
    let state = state_for(build_env("bypass", 50));
    let default_config = SimpConfig::new();

    let before = cacheable_rebuild_count();
    let first = collect_simp_lemmas_cached(&state, &default_config);
    assert_eq!(cacheable_rebuild_count(), before + 1);

    // `simp only [lemma]` resolves names against the local context and opened
    // namespaces — goal-dependent, so it must bypass the cache entirely (no
    // counted rebuild, no cache pollution).
    let mut only_config = SimpConfig::new();
    only_config.only = true;
    only_config.extra_lemmas = vec![perf_lemma_name("bypass", 0).to_string()];
    let only_set = collect_simp_lemmas_cached(&state, &only_config);
    assert!(
        only_set.len() < first.len(),
        "simp-only set must not be served from the full-set cache"
    );
    assert_eq!(
        cacheable_rebuild_count(),
        before + 1,
        "bypassed configs are not cacheable rebuilds"
    );

    // The default-config entry must still be cached after the bypass.
    let again = collect_simp_lemmas_cached(&state, &default_config);
    assert_eq!(cacheable_rebuild_count(), before + 1);
    assert!(Arc::ptr_eq(&first, &again));
}

#[test]
fn test_simp_candidates_const_headed_query_consults_fewer_lemmas() {
    let state = state_for(build_env("cands", 1000));
    let goal = state
        .current_goal()
        .expect("proof state should have a goal")
        .clone();
    let set = collect_simp_lemmas_cached(&state, &SimpConfig::new());
    let total = set.len();

    let zz_name = Name::from_string("SimpPerf.eq_zz_refl");
    let flip_name = Name::from_string("SimpPerf.eq_flip");

    // Eq-headed subterm: tree match (SimpPerf.eq_zz_refl) + the Eq head bucket
    // (SimpPerf.eq_flip) + the headless remainder — NOT the 1000-lemma scan.
    let eq_query = mk_eq_nat(nat_zero(), nat_zero());
    let eq_candidates = set.candidates(&state, &goal, &eq_query);
    assert!(
        eq_candidates.len() < total,
        "Eq-headed query consulted {} of {total} lemmas — expected strictly fewer",
        eq_candidates.len()
    );
    assert!(
        eq_candidates.iter().any(|l| l.name == zz_name),
        "tree-indexed Eq-rooted lemma must be offered at an Eq-headed query"
    );
    assert!(
        eq_candidates.iter().any(|l| l.name == flip_name),
        "Eq-bucketed star lemma must stay reachable at an Eq-headed query"
    );

    // c5-headed subterm: its own tree lemma, its (empty) head bucket, and the
    // headless remainder — the Eq bucket must not be dragged in.
    let c5_lemma = perf_lemma_name("cands", 5);
    let c5_query = Expr::const_(perf_const_name("cands", 5), vec![]);
    let c5_candidates = set.candidates(&state, &goal, &c5_query);
    assert!(
        c5_candidates.len() < total,
        "Const-headed query consulted {} of {total} lemmas — expected strictly fewer",
        c5_candidates.len()
    );
    assert!(
        c5_candidates.iter().any(|l| l.name == c5_lemma),
        "the lemma indexed under the query's own head must be offered"
    );
    assert!(
        !c5_candidates.iter().any(|l| l.name == flip_name),
        "an Eq-bucketed lemma must not be scanned at a non-Eq-headed query"
    );
}

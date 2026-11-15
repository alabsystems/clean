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
/// The `salt` keeps each test's declarations distinct. Cache identity also
/// separates fresh environments whose declarations reuse the same names.
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
fn test_simp_cache_separates_divergent_clones_with_the_same_registry_names() {
    let mut base = build_env("branch", 0);
    let heads = ["SimpPerf.branch.left", "SimpPerf.branch.right"];
    for head in heads {
        base.add_decl(Declaration::Axiom {
            name: Name::from_string(head),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
        })
        .expect("register branch head");
    }
    let mut states = Vec::new();
    let lemma = Name::from_string("SimpPerf.branch.same_lemma");
    for head in heads {
        let mut env = base.clone();
        env.add_decl(Declaration::Axiom {
            name: lemma.clone(),
            level_params: vec![],
            type_: mk_eq_nat(Expr::const_(Name::from_string(head), vec![]), nat_zero()),
        })
        .expect("register a different statement under the same lemma name");
        env.register_simp_lemma(lemma.clone(), SimpPriority::Default);
        states.push(state_for(env));
    }
    assert_eq!(states[0].env().generation(), states[1].env().generation());
    assert_eq!(
        states[0].env().simp_registry_revision(),
        states[1].env().simp_registry_revision()
    );
    let config = SimpConfig::new();
    let first = collect_simp_lemmas_cached(&states[0], &config);
    let second = collect_simp_lemmas_cached(&states[1], &config);
    assert!(!Arc::ptr_eq(&first, &second));
    for (set, head) in [(&first, heads[0]), (&second, heads[1])] {
        let rule = set
            .iter()
            .find(|rule| rule.name == lemma)
            .expect("own lemma");
        assert_eq!(rule.lhs, Expr::const_(Name::from_string(head), vec![]));
    }
    assert!(Arc::ptr_eq(
        &first,
        &collect_simp_lemmas_cached(&states[0], &config)
    ));
}

#[test]
fn test_simp_cache_recomputes_paths_for_an_independent_environment() {
    use crate::tactic::simp::path_computation_count;

    let config = SimpConfig::new();
    let first = state_for(build_env("independent", 5));
    let second = state_for(build_env("independent", 5));
    let before = path_computation_count();
    let first_set = collect_simp_lemmas_cached(&first, &config);
    let first_computed = path_computation_count() - before;
    assert!(first_computed > 0);
    let before = path_computation_count();
    let second_set = collect_simp_lemmas_cached(&second, &config);
    assert_eq!(path_computation_count() - before, first_computed);
    assert!(!Arc::ptr_eq(&first_set, &second_set));
}

#[test]
fn test_simp_cache_rebuilds_after_trusted_registry_delta_replay() {
    use clean_kernel::env::TrustedEnvExt;

    let lemma = perf_lemma_name("delta", 0);
    let mut env = build_env("delta", 1);
    assert!(env.unregister_simp_lemma(&lemma));
    let mut state = state_for(env);
    let config = SimpConfig::new();
    for action in 0..3 {
        let old = collect_simp_lemmas_cached(&state, &config);
        let identity = state.env().simp_cache_identity();
        let mut produced = state.env().clone();
        match action {
            0 => produced.register_simp_lemma(lemma.clone(), SimpPriority::Default),
            1 => assert!(produced.unregister_simp_lemma(&lemma)),
            _ => {
                produced.register_simp_lemma(lemma.clone(), SimpPriority::Default);
                assert!(produced.unregister_simp_lemma(&lemma));
            }
        }
        let delta = produced
            .local_fact_delta_since(state.env())
            .expect("actual checked registry delta");
        if action == 0 {
            let mut wrong_base = state.env().clone();
            wrong_base.register_simp_lemma(lemma.clone(), SimpPriority::Default);
            let unchanged = wrong_base.simp_cache_identity();
            let bytes = wrong_base.to_bincode().expect("record wrong base");
            assert!(TrustedEnvExt::apply_local_fact_delta(&mut wrong_base, &delta).is_err());
            assert_eq!(unchanged, wrong_base.simp_cache_identity());
            assert_eq!(
                bytes,
                wrong_base.to_bincode().expect("unchanged wrong base")
            );
        }
        TrustedEnvExt::apply_local_fact_delta(state.env_mut(), &delta)
            .expect("replay through the actual trusted endpoint");
        assert_ne!(identity, state.env().simp_cache_identity());
        let rebuilds = cacheable_rebuild_count();
        let new = collect_simp_lemmas_cached(&state, &config);
        assert_eq!(cacheable_rebuild_count(), rebuilds + 1);
        assert!(!Arc::ptr_eq(&old, &new));
        assert_eq!(new.iter().any(|rule| rule.name == lemma), action == 0);
        assert!(Arc::ptr_eq(
            &new,
            &collect_simp_lemmas_cached(&state, &config)
        ));
        assert_eq!(cacheable_rebuild_count(), rebuilds + 1);
    }
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

/// A registry that GROWS must be seen (the rebuild above) — and the rebuild
/// must pay path computation for the new lemma only, while building exactly
/// the set a from-scratch build does. Every `@[simp]` declaration of a file
/// is such a growth; re-deriving ~10k imported key paths per growth was 27%
/// of one `Mathlib/Logic/Basic.lean` sample (performance audit 2026-09-24).
#[test]
fn test_simp_cache_rebuild_on_growth_computes_only_the_new_paths() {
    use crate::tactic::simp::{collect_simp_lemmas, path_computation_count};

    let env = build_env("memo", 50);
    let config = SimpConfig::new();
    let state = state_for(env.clone());
    let first = collect_simp_lemmas_cached(&state, &config);

    let mut grown = env;
    let late_head = Name::from_string("SimpPerf.memo.lateHead");
    grown
        .add_decl(Declaration::Axiom {
            name: late_head.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
        })
        .expect("register late head");
    let late = Name::from_string("SimpPerf.memo.late");
    grown
        .add_decl(Declaration::Axiom {
            name: late.clone(),
            level_params: vec![],
            type_: mk_eq_nat(Expr::const_(late_head.clone(), vec![]), nat_zero()),
        })
        .expect("register late lemma");
    grown.register_simp_lemma(late.clone(), SimpPriority::Default);
    let grown_state = state_for(grown);

    let computed_before = path_computation_count();
    let rebuilt = collect_simp_lemmas_cached(&grown_state, &config);
    let computed = path_computation_count() - computed_before;
    assert_eq!(
        computed,
        1,
        "the rebuild must compute the new lemma's path and reuse the {} it had",
        first.len()
    );

    // The same set a from-scratch build makes: same lemmas in the same order,
    // and the same candidates at the new lemma's head and at old ones.
    let scratch = collect_simp_lemmas(&grown_state, &config);
    let rebuilt_names: Vec<Name> = rebuilt.iter().map(|l| l.name.clone()).collect();
    let scratch_names: Vec<Name> = scratch.iter().map(|l| l.name.clone()).collect();
    assert_eq!(rebuilt_names, scratch_names);
    let goal = grown_state.current_goal().expect("a goal").clone();
    for query in [
        Expr::const_(late_head.clone(), vec![]),
        Expr::const_(perf_const_name("memo", 7), vec![]),
        mk_eq_nat(nat_zero(), nat_zero()),
    ] {
        let from_memo: Vec<Name> = rebuilt
            .candidates(&grown_state, &goal, &query)
            .iter()
            .map(|l| l.name.clone())
            .collect();
        let from_scratch: Vec<Name> = scratch
            .candidates(&grown_state, &goal, &query)
            .iter()
            .map(|l| l.name.clone())
            .collect();
        assert_eq!(from_memo, from_scratch, "candidates differ at {query:?}");
    }
    assert!(
        rebuilt
            .candidates(&grown_state, &goal, &Expr::const_(late_head, vec![]))
            .iter()
            .any(|l| l.name == late),
        "the new lemma must be offered at its own head"
    );
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
    only_config.extra_lemmas = vec![clean_parser::SurfaceName::from_name(perf_lemma_name(
        "bypass", 0,
    ))];
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

/// `simp at h` sets `SimpConfig::exclude_hypothesis` for every hypothesis it
/// visits. That flag is read only by the two channels a cacheable config
/// already has empty (`extra_lemmas`, and `collect_hypothesis_lemmas` behind
/// `use_hypotheses`), so it must not disqualify the cache: while it did, the
/// commonest simp spelling of all fell to the composable arm, where
/// `SimpLemmaSet::base_with_overlay` deep-clones the base — ~10k lemmas and
/// the discrimination tree under real imports — to add an empty overlay.
#[test]
fn test_simp_cache_excluded_hypothesis_still_hits_the_cache() {
    let state = state_for(build_env("excl", 1000));
    let plain = SimpConfig::new();
    let mut excluded = SimpConfig::new();
    excluded.exclude_hypothesis = Some(clean_parser::SurfaceName::generated_path("h"));

    let before = cacheable_rebuild_count();
    let first = collect_simp_lemmas_cached(&state, &plain);
    let second = collect_simp_lemmas_cached(&state, &excluded);

    assert_eq!(
        cacheable_rebuild_count(),
        before + 1,
        "a config that only carries `exclude_hypothesis` must reuse the cached set"
    );
    assert!(
        Arc::ptr_eq(&first, &second),
        "the excluded-hypothesis config must get the identical Arc, not a clone"
    );
}

/// The control: a config whose `extra_lemmas` are non-empty is genuinely not
/// cacheable, so the relaxation above cannot be hiding a real overlay.
#[test]
fn test_simp_cache_extra_lemmas_still_bypass_the_cache() {
    let state = state_for(build_env("excl_ctl", 50));
    let plain = SimpConfig::new();
    let mut extras = SimpConfig::new();
    extras.extra_lemmas = vec![clean_parser::SurfaceName::generated_path("SimpPerf.l0")];

    let first = collect_simp_lemmas_cached(&state, &plain);
    let second = collect_simp_lemmas_cached(&state, &extras);
    assert!(
        !Arc::ptr_eq(&first, &second),
        "a config carrying extra lemmas must not be served the bare cached set"
    );
}

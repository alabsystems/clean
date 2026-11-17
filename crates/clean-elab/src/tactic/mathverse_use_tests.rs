// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `mathverse_use` and `mathverse_suggest` tactics.

use clean_kernel::{Environment, Expr, Level};

use super::mathverse_use::{eval_mathverse_suggest, eval_mathverse_use};
use super::{ProofState, TacticError};

#[test]
fn test_mathverse_use_no_goals_returns_error() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    // Close the goal so no goals remain
    let _ = super::sorry(&mut state);
    assert!(state.is_complete());

    let result = eval_mathverse_use(&mut state, &[]);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_suggest_no_goals_returns_error() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    let _ = super::sorry(&mut state);
    assert!(state.is_complete());

    let result = eval_mathverse_suggest(&mut state, &[]);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_use_without_library_returns_search_exhausted() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    let result = eval_mathverse_use(&mut state, &[]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    match &err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_use");
            // Either "not enabled" or "no Mathverse Library loaded" depending on feature
            assert!(
                detail.contains("mathverse") || detail.contains("Mathverse"),
                "detail should mention mathverse: {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

#[test]
fn test_mathverse_suggest_without_library_returns_search_exhausted() {
    let env = Environment::new();
    let target = Expr::sort(Level::zero());
    let mut state = ProofState::new(env, target);

    let result = eval_mathverse_suggest(&mut state, &[]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    match &err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_suggest");
            assert!(
                detail.contains("mathverse") || detail.contains("Mathverse"),
                "detail should mention mathverse: {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

#[test]
fn test_mathverse_use_registered_in_builtins() {
    // Verify the tactics are registered by building a fresh registry
    let patterns = super::builtins::builtin_tactic_patterns();

    assert!(
        patterns.contains_key("mathverse_use"),
        "mathverse_use should be registered in builtin tactics"
    );
    assert!(
        patterns.contains_key("mathverse_suggest"),
        "mathverse_suggest should be registered in builtin tactics"
    );
}

// Trust gate tests (require mathverse-library feature).

#[cfg(feature = "mathverse-library")]
mod trust_gate_tests;

// Disc-tree regression tests for #3412.
//
// These tests pin the tactic-layer wiring: eval_mathverse_suggest (and thus
// eval_mathverse_use) populate goal_type_idx and exercise the discrimination
// tree. The library side of this fix is covered in
// `clean-mathverse::premise_select` tests; these tests are a tactic-layer guard
// that future refactors do not regress the disc-tree query path back to
// None-only, name-only search.
//
// Distinguishing disc-tree from name/BM25/symbol-overlap channels is done by
// using a candidate whose stored name shares zero tokens with the goal's
// extracted symbols. The only channel that can surface it is the disc tree.

#[cfg(feature = "mathverse-library")]
mod disc_tree_tactic_wiring;

#[cfg(feature = "mathverse-library")]
mod native_replay_gate;

// ---------------------------------------------------------------------------
// UNIT REPRODUCTION of the universe-polymorphic citation failure.
//
// Deliberately uses NO mathverse machinery — no shard, no library, no trust
// gate. The failure is in `mk_const` + `exact` alone, and isolating it here
// turns a 75-second rebuild-plus-shard-load into a millisecond test.
// ---------------------------------------------------------------------------

/// `Poly.{u} : ∀ (A : Sort u), A → A`, proved by `fun A a => a`.
#[cfg(feature = "mathverse-library")]
fn register_poly_id(env: &mut Environment) -> clean_kernel::name::Name {
    use clean_kernel::name::Name;
    use clean_kernel::{BinderInfo, Declaration};
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    // ∀ (A : Sort u), A → A
    let ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    // fun (A : Sort u) (a : A) => a
    let val = Expr::lam(
        BinderInfo::Default,
        sort_u,
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let name = Name::from_string("Poly.id");
    // Definition, not Theorem: `∀ (A : Sort u), A → A` lives in
    // `IMax(Succ(..), u)`, not Prop, and the kernel rightly rejects a Theorem
    // whose type is not a proposition.
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![u],
        type_: ty,
        value: val,
        is_reducible: false,
    })
    .expect("fixture must register");
    name
}

/// A universe-MONOMORPHIC citation closes its own type. Control case: proves
/// the harness itself is sound, so a failure below is about universes only.
#[cfg(feature = "mathverse-library")]
#[test]
fn test_exact_mk_const_closes_monomorphic_own_type() {
    use clean_kernel::name::Name;
    use clean_kernel::{BinderInfo, Declaration};
    let mut env = Environment::new();
    // ∀ (P : Prop), P → P   proved by   fun P p => p
    // (NOT `∀ P, P` — that is false, and the kernel correctly refused it.)
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let val = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let name = Name::from_string("Mono.id");
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: ty.clone(),
        value: val,
    })
    .expect("fixture registers");

    let mut state = ProofState::new(env, ty);
    let e = state.mk_const(&name);
    super::exact(&mut state, e).expect("monomorphic citation of its own type must close");
}

/// THE REPRODUCTION: a universe-POLYMORPHIC citation of its own type.
///
/// `mk_const` instantiates `Poly.id`'s `u` with a fresh `u_0`, while the goal
/// carries the declared `u`, so `exact` compares `Sort(Param(u_0))` against
/// `Sort(Param(u))`. Both are `Level::Param`; `unify_levels` must reconcile
/// them by assigning the fresh one.
#[cfg(feature = "mathverse-library")]
#[test]
fn test_exact_mk_const_closes_universe_polymorphic_own_type() {
    let mut env = Environment::new();
    let name = register_poly_id(&mut env);
    let ty = env.get_const(&name).expect("registered").type_.clone();

    let mut state = ProofState::new(env, ty);
    let e = state.mk_const(&name);
    super::exact(&mut state, e).expect(
        "citing a universe-polymorphic constant against its OWN type must close: \
         mk_const's fresh universe param has to unify with the goal's declared one",
    );
}

/// Tests for the FABRICATED-STUB discharge that lets a citation rest on the
/// shard's genuine declaration instead of a hand-rolled prelude carrier.
///
/// The measured instance is `Fact`: `Environment::with_prelude` seeds
/// `Fact`/`Fact.mk`/`Fact.out` as bare `Declaration::Axiom`s, while Mathlib
/// declares `class Fact (p : Prop) : Prop where out : p`. These tests pin the
/// PREDICATE — which stubs may be retired and which must never be — because a
/// discharge that is one notch too wide silently deletes a genuine axiom, and
/// one notch too narrow leaves the citation resting on a fabrication.
#[cfg(feature = "mathverse-library")]
mod fabricated_stub_discharge;

/// Exercise universe rigidity through the real checked Mathverse citation path.
#[cfg(feature = "mathverse-library")]
mod goal_universe_tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the PROVED LRAT (RUP) soundness layer — the AxiomAudit-style
//! guard for `checkLrat_sound`'s axiom budget, matching how
//! `resolution_soundness_tests` gates `checkRefutes3_sound`: every proved
//! lemma must be a kernel-checked `Declaration::Theorem` whose transitive
//! domain-axiom closure (`Environment::axiom_deps`, i.e. everything outside
//! `FOUNDATIONAL_AXIOMS`) is EMPTY.

use super::names;
use crate::name::Name;
use crate::{ConstantKind, Environment};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_lrat_soundness().expect("init_lrat_soundness");
    env.init_lrat_soundness().expect("idempotent");
    env
}

/// Non-foundational axioms reachable from `name`.
fn domain_axioms(env: &Environment, name: &str) -> Vec<String> {
    let mut v: Vec<String> = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(ToString::to_string)
        .collect();
    v.sort();
    v
}

fn assert_proved_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "{name} must be a Theorem; got {:?}",
        info.kind
    );
    let axs = domain_axioms(env, name);
    assert!(
        axs.is_empty(),
        "{name} must have empty domain-axiom closure; got {axs:?}"
    );
}

#[test]
fn test_all_lrat_lemmas_are_proved_theorems_foundational() {
    // The AxiomAudit-style budget gate: every lemma in the LRAT soundness
    // chain is a kernel-checked Theorem with closure ⊆ FOUNDATIONAL_AXIOMS.
    let env = env();
    for n in [
        names::MEM_ALL_NOT_HOLDS,
        names::CLAUSE_OR_DECIDE,
        names::LRAT_REDUCE_SAT,
        names::LRAT_RUP_SOUND,
        names::CHECK_LRAT_STEP_SAT,
        names::GO_LRAT_SOUND,
        names::CHECK_LRAT_SOUND,
    ] {
        assert_proved_theorem(&env, n);
    }
}

#[test]
fn test_check_lrat_sound_is_proved_theorem_with_empty_domain_axioms() {
    // THE HEADLINE (CK1 WS1-M2): checkLrat_sound is a kernel-checked Theorem
    // with ZERO residual domain-specific axioms — the LRAT checker carries the
    // SAME trust story as checkRefutes3_sound (same clause vocabulary, same
    // `Unsat cs` conclusion, foundational-only closure).
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::CHECK_LRAT_SOUND))
        .expect("checkLrat_sound registered");
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "checkLrat_sound must be a PROVED Theorem, not a stated Axiom"
    );
    let axs = domain_axioms(&env, names::CHECK_LRAT_SOUND);
    assert!(
        axs.is_empty(),
        "checkLrat_sound must have empty domain-axiom closure (fully zero-trust); got {axs:?}"
    );
}

#[test]
fn test_all_not_holds_is_definition_not_axiom() {
    // The falsified-set invariant is a real model Definition (Bool-only
    // membership on the computational side; And-fold of (H l → False) on the
    // Prop side) — not an opaque axiom.
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::ALL_NOT_HOLDS))
        .expect("allNotHolds should be registered");
    assert!(
        matches!(info.kind, ConstantKind::Definition),
        "allNotHolds must be a Definition (real model semantics), not an axiom; got {:?}",
        info.kind
    );
}

#[test]
fn test_lrat_and_resolution_soundness_share_the_unsat_vocabulary() {
    // Both bridges must conclude in the SAME `Unsat` (one unsatisfiability
    // notion across checkRefutes3 and checkLrat) — pin the shared semantic
    // definitions to Definitions in the LRAT env.
    use crate::resolution_soundness::names as snames;
    let env = env();
    for n in [
        snames::UNSAT,
        snames::ALL_SAT,
        snames::RES_CONSISTENT,
        snames::RES_EXCLUSIVE,
        snames::ALL_SAT_TRIE,
    ] {
        let info = env
            .get_const(&Name::from_string(n))
            .unwrap_or_else(|| panic!("{n} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{n} must be a Definition; got {:?}",
            info.kind
        );
    }
    // And the resolution bridge itself must still be present + foundational in
    // the same environment (the two checkers coexist).
    assert_proved_theorem(&env, snames::CHECK_REFUTES3_SOUND);
}

/// End-to-end: the reflection certificate `Eq.refl Bool.true` type-checks
/// against `checkLrat (initialTrie cs) (listLen cs) trace = true` — the EXACT
/// hypothesis shape `checkLrat_sound` consumes — in an environment where the
/// soundness theorem is registered.
#[test]
fn test_eq_refl_cert_typechecks_against_check_lrat_sound_hypothesis() {
    use crate::lrat_check::{check_lrat_initialtrie_app, LratStepData};
    use crate::resolution_check::encode_clauses;
    use crate::{Expr, Level, TypeChecker};

    let env = env();
    let clauses: Vec<Vec<(u32, bool)>> = vec![
        vec![(0, false), (1, false)],
        vec![(0, false), (1, true)],
        vec![(0, true), (1, false)],
        vec![(0, true), (1, true)],
    ];
    let trace: Vec<LratStepData> = vec![
        (vec![(0, false)], vec![0, 1]),
        (vec![(0, true)], vec![2, 3]),
        (vec![], vec![4, 5]),
    ];
    let app = check_lrat_initialtrie_app(encode_clauses(&clauses), &trace);
    let bool_ty = Expr::const_str("Bool");
    let btrue = Expr::const_str("Bool.true");
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty.clone(), btrue.clone()],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty, app, btrue],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&proof, &goal)
        .expect("Eq.refl must type-check checkLrat_sound's hypothesis shape");
}

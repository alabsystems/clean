// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the PROVED resolution-soundness layer.

use super::names;
use crate::name::Name;
use crate::{ConstantKind, Environment};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");
    env.init_resolution_soundness().expect("idempotent");
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
fn test_nat_beq_eq_is_proved_theorem_foundational() {
    let env = env();
    assert_proved_theorem(&env, names::NAT_BEQ_EQ);
}

#[test]
fn test_drop_false_sat_is_proved_theorem_foundational() {
    let env = env();
    assert_proved_theorem(&env, names::DROP_FALSE_SAT);
}

#[test]
fn test_append_sat_lemmas_are_proved_theorems_foundational() {
    let env = env();
    assert_proved_theorem(&env, names::APPEND_SAT_L);
    assert_proved_theorem(&env, names::APPEND_SAT_R);
}

#[test]
fn test_resolve_step_sat_is_proved_theorem_foundational() {
    let env = env();
    assert_proved_theorem(&env, names::RESOLVE_STEP_SAT);
}

#[test]
fn test_mem_subset_sat_are_proved_theorems_foundational() {
    let env = env();
    assert_proved_theorem(&env, names::MEM_SAT);
    assert_proved_theorem(&env, names::SUBSET_SAT);
}

#[test]
fn test_all_proved_lemmas_are_theorems_foundational() {
    let env = env();
    for n in [
        names::NAT_BEQ_EQ,
        names::DROP_FALSE_SAT,
        names::APPEND_SAT_L,
        names::APPEND_SAT_R,
        names::RESOLVE_STEP_SAT,
        names::MEM_SAT,
        names::SUBSET_SAT,
        names::SETEQ_SAT,
        names::NTH_SAT,
        names::MEM_NOT_NIL,
        names::CHECK_STEP_SAT,
        names::ALL_SAT_SNOC,
        names::LIST_IS_NIL_SAT,
        names::GO_SOUND,
        names::CHECK_REFUTES_SOUND,
        // §12 trie-checker (checkRefutes3) soundness layer.
        names::TRIE_GET_SAT,
        names::TRIE_INS_PRESERVES_ALL_SAT,
        names::CHECK_STEP3_SAT,
        names::GO3_SOUND,
        names::CHECK_REFUTES3_SOUND,
    ] {
        assert_proved_theorem(&env, n);
    }
}

#[test]
fn test_all_sat_trie_is_definition_not_axiom() {
    use crate::ConstantKind;
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::ALL_SAT_TRIE))
        .expect("allSatTrie should be registered");
    assert!(
        matches!(info.kind, ConstantKind::Definition),
        "allSatTrie must be a Definition (real model semantics), not an axiom; got {:?}",
        info.kind
    );
}

#[test]
fn test_check_refutes3_sound_is_proved_theorem_with_empty_domain_axioms() {
    // THE HEADLINE for the sub-quadratic trie checker: checkRefutes3_sound is a
    // kernel-checked Theorem with ZERO residual domain-specific axioms (closure ⊆
    // FOUNDATIONAL), with the same `Unsat cs` conclusion as checkRefutes_sound.
    use crate::ConstantKind;
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::CHECK_REFUTES3_SOUND))
        .expect("checkRefutes3_sound registered");
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "checkRefutes3_sound must be a PROVED Theorem, not a stated Axiom"
    );
    let axs = domain_axioms(&env, names::CHECK_REFUTES3_SOUND);
    assert!(
        axs.is_empty(),
        "checkRefutes3_sound must have empty domain-axiom closure (fully zero-trust); got {axs:?}"
    );
}

#[test]
fn test_semantics_are_definitions_not_axioms() {
    use crate::ConstantKind;
    let env = env();
    for n in [
        names::ALL_SAT,
        names::RES_CONSISTENT,
        names::RES_EXCLUSIVE,
        names::UNSAT,
    ] {
        let info = env
            .get_const(&Name::from_string(n))
            .unwrap_or_else(|| panic!("{n} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{n} must be a Definition (real model semantics), not an axiom; got {:?}",
            info.kind
        );
    }
}

#[test]
fn test_check_refutes_sound_is_proved_theorem_with_empty_domain_axioms() {
    // THE HEADLINE: the top-level soundness bridge is now a kernel-checked Theorem
    // with ZERO residual domain-specific axioms (closure ⊆ FOUNDATIONAL).
    use crate::ConstantKind;
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::CHECK_REFUTES_SOUND))
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem, not a stated Axiom"
    );
    let axs = domain_axioms(&env, names::CHECK_REFUTES_SOUND);
    assert!(
        axs.is_empty(),
        "checkRefutes_sound must have empty domain-axiom closure (fully zero-trust); got {axs:?}"
    );
}

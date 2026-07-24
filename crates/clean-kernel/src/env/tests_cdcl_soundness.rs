// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CDCL soundness invariant formalization.
//!
//! **#3630 demasquerade status:** S01-S06 were previously registered as
//! `Declaration::Theorem` whose proof terms were lambda wrappers around
//! same-type `_proof` / combinator axioms (the wave-10 MASQUERADE
//! pattern; see `designs/2026-04-19-demasquerade-cxxx-pattern.md`).
//! Per the design doc Proof Soundness Rules ("Declaration::Theorem
//! wrapping Declaration::Axiom is NOT a proof. It is a restatement."),
//! they have been demoted to honest `Declaration::Axiom` on their
//! original Pi types.
//!
//! These tests now validate:
//! - types / transitions / invariants / per-transition step axioms are
//!   registered (unchanged);
//! - S01-S06 are `Declaration::Axiom` (post-demasquerade);
//! - NO axiom-wrapping Theorem masquerade has re-appeared — guard tests
//!   assert the dead `_proof` / combinator axiom names are NOT registered,
//!   and that no S01-S06 claim carries a proof value.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_cdcl_soundness().expect("init_cdcl_soundness");
    env
}

/// S01-S06 top-level CDCL soundness claims (axioms post-demasquerade).
const CDCL_SOUNDNESS_CLAIMS: &[&str] = &[
    "CDCLSoundness.trail_consistency_preserved",
    "CDCLSoundness.two_watched_preserved",
    "CDCLSoundness.resolution_soundness",
    "CDCLSoundness.backtrack_correctness",
    "CDCLSoundness.propagation_completeness",
    "CDCLSoundness.cdcl_terminates",
];

// ====================================================================
// Type registration tests
// ====================================================================

#[test]
fn test_all_types_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.Variable",
        "CDCLSoundness.Literal",
        "CDCLSoundness.Literal.variable",
        "CDCLSoundness.Literal.polarity",
        "CDCLSoundness.Clause",
        "CDCLSoundness.Clause.size",
        "CDCLSoundness.Assignment",
        "CDCLSoundness.TrailEntry",
        "CDCLSoundness.TrailEntry.literal",
        "CDCLSoundness.TrailEntry.level",
        "CDCLSoundness.Trail",
        "CDCLSoundness.Trail.length",
        "CDCLSoundness.WatchList",
        "CDCLSoundness.CDCLState",
        "CDCLSoundness.CDCLState.assignment",
        "CDCLSoundness.CDCLState.trail",
        "CDCLSoundness.CDCLState.watches",
        "CDCLSoundness.CDCLState.clauses",
        "CDCLSoundness.CDCLState.learned",
        "CDCLSoundness.CDCLState.decision_level",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

// ====================================================================
// State transition registration tests
// ====================================================================

#[test]
fn test_all_transitions_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.Propagate",
        "CDCLSoundness.Decide",
        "CDCLSoundness.Conflict",
        "CDCLSoundness.Backtrack",
        "CDCLSoundness.Restart",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

// ====================================================================
// Invariant predicate registration tests
// ====================================================================

#[test]
fn test_all_invariants_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.trail_consistent",
        "CDCLSoundness.two_watched_invariant",
        "CDCLSoundness.conflict_derivation_sound",
        "CDCLSoundness.backtrack_correct",
        "CDCLSoundness.propagation_complete",
        "CDCLSoundness.termination_measure",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

// ====================================================================
// Claim registration tests -- S01-S06 are honest Declaration::Axiom
// (post-#3630 demasquerade)
// ====================================================================

#[test]
fn test_all_claims_registered() {
    let env = make_env();
    for name in CDCL_SOUNDNESS_CLAIMS {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_all_helpers_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.trail_consistency_preserved_helper",
        "CDCLSoundness.two_watched_preserved_helper",
        "CDCLSoundness.resolution_soundness_helper",
        "CDCLSoundness.backtrack_correctness_helper",
        "CDCLSoundness.propagation_completeness_helper",
        "CDCLSoundness.cdcl_terminates_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered",
        );
    }
}

// ====================================================================
// Per-transition induction step axiom tests
// ====================================================================

#[test]
fn test_s01_induction_step_axioms_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.propagate_preserves_trail",
        "CDCLSoundness.decide_preserves_trail",
        "CDCLSoundness.conflict_preserves_trail",
        "CDCLSoundness.restart_preserves_trail",
        "CDCLSoundness.backtrack_preserves_trail",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "S01 induction step axiom {name} should be registered",
        );
    }
}

#[test]
fn test_s02_induction_step_axioms_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.propagate_preserves_2wl",
        "CDCLSoundness.decide_preserves_2wl",
        "CDCLSoundness.conflict_preserves_2wl",
        "CDCLSoundness.restart_preserves_2wl",
        "CDCLSoundness.backtrack_preserves_2wl",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "S02 induction step axiom {name} should be registered",
        );
    }
}

#[test]
fn test_s03_induction_step_axioms_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.resolution_step_sound",
        "CDCLSoundness.propagate_preserves_resolution",
        "CDCLSoundness.decide_preserves_resolution",
        "CDCLSoundness.restart_preserves_resolution",
        "CDCLSoundness.backtrack_preserves_resolution",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "S03 induction step axiom {name} should be registered",
        );
    }
}

#[test]
fn test_s04_induction_step_axiom_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("CDCLSoundness.backtrack_step_correct"))
            .is_some(),
        "S04 induction step axiom should be registered",
    );
}

#[test]
fn test_s05_induction_step_axiom_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("CDCLSoundness.bcp_fixpoint_complete"))
            .is_some(),
        "S05 induction step axiom should be registered",
    );
}

#[test]
fn test_s06_induction_step_axioms_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.measure_decreases",
        "CDCLSoundness.conflict_decreases_measure",
        "CDCLSoundness.measure_well_founded",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "S06 induction step axiom {name} should be registered",
        );
    }
}

// ====================================================================
// Type checking tests
// ====================================================================

#[test]
fn test_cdcl_state_type_checks() {
    let env = make_env();
    let state = crate::expr::Expr::const_(Name::from_string("CDCLSoundness.CDCLState"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&state)
        .expect("infer CDCLSoundness.CDCLState type");
    // CDCLState : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_trail_consistent_type_checks() {
    let env = make_env();
    let tc_const =
        crate::expr::Expr::const_(Name::from_string("CDCLSoundness.trail_consistent"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&tc_const)
        .expect("infer CDCLSoundness.trail_consistent type");
    // trail_consistent : CDCLState -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_backtrack_type_checks() {
    let env = make_env();
    let bt = crate::expr::Expr::const_(Name::from_string("CDCLSoundness.Backtrack"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&bt)
        .expect("infer CDCLSoundness.Backtrack type");
    // Backtrack : CDCLState -> Nat -> CDCLState (Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_backtrack_correctness_type_checks() {
    let env = make_env();
    let bt_thm = crate::expr::Expr::const_(
        Name::from_string("CDCLSoundness.backtrack_correctness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&bt_thm)
        .expect("infer CDCLSoundness.backtrack_correctness type");
    // forall (s : CDCLState) (k : Nat) (s' : CDCLState), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_propagation_completeness_type_checks() {
    let env = make_env();
    let pc = crate::expr::Expr::const_(
        Name::from_string("CDCLSoundness.propagation_completeness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&pc)
        .expect("infer CDCLSoundness.propagation_completeness type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Classification tests
// ====================================================================

#[test]
fn test_types_and_transitions_are_axioms() {
    let env = make_env();
    let axiom_names = [
        "CDCLSoundness.Variable",
        "CDCLSoundness.Literal",
        "CDCLSoundness.Clause",
        "CDCLSoundness.Assignment",
        "CDCLSoundness.Trail",
        "CDCLSoundness.TrailEntry",
        "CDCLSoundness.WatchList",
        "CDCLSoundness.CDCLState",
        "CDCLSoundness.Propagate",
        "CDCLSoundness.Decide",
        "CDCLSoundness.Conflict",
        "CDCLSoundness.Backtrack",
        "CDCLSoundness.Restart",
        "CDCLSoundness.trail_consistent",
        "CDCLSoundness.two_watched_invariant",
        "CDCLSoundness.conflict_derivation_sound",
        "CDCLSoundness.backtrack_correct",
        "CDCLSoundness.propagation_complete",
        "CDCLSoundness.termination_measure",
    ];
    for name in axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

/// Post-#3630 demasquerade: every S01-S06 top-level claim is an honest
/// `Declaration::Axiom` on its original Pi type, not a Theorem wrapping
/// a same-type axiom with a lambda value.
#[test]
fn test_soundness_claims_are_honest_axioms_not_masqueraded_theorems() {
    let env = make_env();
    for name in CDCL_SOUNDNESS_CLAIMS {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "{name} should be a Declaration::Axiom post-#3630 demasquerade \
             (design doc Proof Soundness Rules: 'Theorem wrapping Axiom is \
             NOT a proof, it is a restatement')"
        );
        assert!(
            info.value.is_none(),
            "{name} must not carry a proof value — axioms have no bodies"
        );
        // Type must still be a Pi (forall (s s' : CDCLState), helper s s').
        assert!(
            matches!(info.type_.kind(), ExprKind::Pi(..)),
            "{name} type should still be a Pi, got {:?}",
            info.type_.kind()
        );
    }
}

/// Guard: the dead `_proof` axioms and combinator axioms that existed
/// as masquerade scaffolding prior to #3630 must NOT be registered after
/// demasquerade. If this regresses, a new MASQUERADE site has been
/// introduced.
#[test]
fn test_dead_masquerade_axioms_are_not_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.trail_consistency_preserved_proof",
        "CDCLSoundness.two_watched_preserved_proof",
        "CDCLSoundness.resolution_soundness_proof",
        "CDCLSoundness.backtrack_correctness_proof",
        "CDCLSoundness.propagation_completeness_proof",
        "CDCLSoundness.cdcl_terminates_proof",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} must NOT be registered — it was a same-type proof axiom \
             used only to wrap Theorem-masquerade values (#3630). Its \
             presence indicates a regression of the wave-10 masquerade \
             pattern."
        );
    }
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // Bare names should NOT exist
    for name in [
        "Variable",
        "Literal",
        "CDCLState",
        "Propagate",
        "trail_consistent",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without CDCLSoundness. prefix",
        );
    }
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_cdcl_soundness().expect("first init");
    env.init_cdcl_soundness().expect("second init (idempotent)");
}

// ====================================================================
// TransitionTag infrastructure tests
// ====================================================================

#[test]
fn test_transition_tag_type_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("CDCLSoundness.TransitionTag"))
        .expect("TransitionTag should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
    // TransitionTag : Type 0
    assert!(matches!(info.type_.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_transition_tag_constructors_registered() {
    let env = make_env();
    for name in [
        "CDCLSoundness.propagate_tag",
        "CDCLSoundness.decide_tag",
        "CDCLSoundness.conflict_tag",
        "CDCLSoundness.restart_tag",
        "CDCLSoundness.backtrack_tag",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("tag constructor {name} should be registered"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
        // Each constructor has type TransitionTag (a Const, not a Pi)
        assert!(
            matches!(info.type_.kind(), ExprKind::Const(..)),
            "{name} type should be TransitionTag (Const), got {:?}",
            info.type_.kind()
        );
    }
}

#[test]
fn test_transition_tag_cases_on_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("CDCLSoundness.TransitionTag.cases_on"))
        .expect("cases_on should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
    // cases_on : forall (C : TransitionTag -> Prop), ... -> forall (t : TransitionTag), C t
    assert!(matches!(info.type_.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_apply_transition_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("CDCLSoundness.apply_transition"))
        .expect("apply_transition should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
    // apply_transition : TransitionTag -> CDCLState -> CDCLState
    assert!(matches!(info.type_.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_valid_transition_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("CDCLSoundness.valid_transition"))
        .expect("valid_transition should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
    // valid_transition : CDCLState -> CDCLState -> TransitionTag -> Prop
    assert!(matches!(info.type_.kind(), ExprKind::Pi(..)));
}

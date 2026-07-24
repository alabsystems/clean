// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed unit tests for the shared certifying-verification bridge skeleton
//! ([`super`]). Every test that exercises a refusal asserts the SPECIFIC
//! [`BridgeError`] variant — a skeleton that fails for the wrong reason is as
//! bad as one that does not fail.

use super::*;
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr};

/// A non-zero source hash with a recognizable byte pattern.
fn hash(seed: u8) -> SourceHash {
    SourceHash([seed; 32])
}

/// A well-formed envelope (all structural invariants satisfied) for the
/// happy-path / gate-specific tests to mutate.
fn good_envelope() -> CertEnvelope {
    CertEnvelope {
        witness: vec![1, 2, 3, 4],
        claimed_verdict: ClaimedVerdict::Holds,
        source_hashes: vec![hash(0xAB), hash(0xCD)],
        residual_tcb: "netlist→CNF Tseitin encoder unverified".to_string(),
        leg: Leg::SoundnessOnly,
    }
}

// ── GATE 1: ingest fail-closed ───────────────────────────────────────────────

#[test]
fn ingest_accepts_a_well_formed_envelope() {
    let cert = ingest(good_envelope()).expect("well-formed envelope ingests");
    // De-duplicated, sorted, both hashes retained.
    assert_eq!(cert.pinned_hashes().len(), 2);
    assert_eq!(cert.envelope().leg, Leg::SoundnessOnly);
}

#[test]
fn empty_witness_is_refused() {
    let mut e = good_envelope();
    e.witness.clear();
    assert_eq!(ingest(e).unwrap_err(), BridgeError::EmptyWitness);
}

#[test]
fn missing_source_hashes_are_refused() {
    let mut e = good_envelope();
    e.source_hashes.clear();
    assert_eq!(ingest(e).unwrap_err(), BridgeError::NoSourceHashes);
}

#[test]
fn forged_zero_source_hash_is_refused() {
    let mut e = good_envelope();
    // Splice in the sentinel zero digest — a forged / absent source object.
    e.source_hashes.push(SourceHash([0u8; 32]));
    assert_eq!(ingest(e).unwrap_err(), BridgeError::ZeroSourceHash);
}

#[test]
fn empty_residual_tcb_is_refused_anti_inflation() {
    let mut e = good_envelope();
    e.residual_tcb = "   ".to_string(); // whitespace-only counts as empty
    assert_eq!(ingest(e).unwrap_err(), BridgeError::EmptyResidualTcb);
}

// ── GATE 2: hash-pin fail-closed (the §3 wrong-artifact trap) ─────────────────

#[test]
fn hash_pin_matches_when_reencode_agrees() {
    let cert = ingest(good_envelope()).unwrap();
    // Checker re-derives the SAME hashes from spec_src (order/dup irrelevant).
    hash_pin(&cert, &[hash(0xCD), hash(0xAB), hash(0xAB)]).expect("matching hashes pin");
}

#[test]
fn hash_pin_mismatch_is_refused() {
    let cert = ingest(good_envelope()).unwrap();
    // Checker re-derived a DIFFERENT source object — wrong artifact.
    let err = hash_pin(&cert, &[hash(0xAB), hash(0x99)]).unwrap_err();
    assert!(matches!(err, BridgeError::HashMismatch(_)), "got {err:?}");
}

// ── GATE 4: axiom_deps ⊆ FOUNDATIONAL, over the REAL kernel ───────────────────

/// Register `True.intro : True` and friends, then a trivial theorem with an
/// EMPTY domain-axiom closure, and confirm the gate accepts it.
#[test]
fn axiom_subset_gate_accepts_a_zero_trust_theorem() {
    let env = Environment::with_prelude();
    // `True.intro` is a constructor of `True`; its closure is foundational/empty.
    // We audit it directly as the "acceptance theorem" stand-in.
    let gate = axiom_deps_subset_foundational(&env, "True.intro", &[]);
    assert!(
        gate.is_ok(),
        "True.intro carries no domain axioms: {gate:?}"
    );
}

/// A theorem that transitively depends on a DOMAIN axiom must be REFUSED by the
/// gate, naming the offending axiom.
#[test]
fn axiom_subset_gate_refuses_a_domain_axiom() {
    let mut env = Environment::with_prelude();
    // Register a domain axiom `bogusAx : True` and a Theorem that uses it as its
    // proof. Its `axiom_deps` is then `{ bogusAx }` (non-foundational).
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bogusAx"),
        level_params: vec![],
        type_: Expr::const_str("True"),
    })
    .expect("register domain axiom");
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("usesBogus"),
        level_params: vec![],
        type_: Expr::const_str("True"),
        value: Expr::const_str("bogusAx"),
    })
    .expect("register theorem using the domain axiom");

    let err = axiom_deps_subset_foundational(&env, "usesBogus", &[]).unwrap_err();
    match err {
        BridgeError::NonFoundationalAxioms { theorem, axioms } => {
            assert_eq!(theorem, "usesBogus");
            assert!(
                axioms.iter().any(|a| a == "bogusAx"),
                "must name the domain axiom; got {axioms:?}"
            );
        }
        other => panic!("expected NonFoundationalAxioms, got {other:?}"),
    }
}

#[test]
fn axiom_subset_gate_refuses_an_unregistered_theorem() {
    let env = Environment::with_prelude();
    let err = axiom_deps_subset_foundational(&env, "Nonexistent.theorem", &[]).unwrap_err();
    assert_eq!(
        err,
        BridgeError::TheoremNotRegistered("Nonexistent.theorem".to_string())
    );
}

#[test]
fn axiom_subset_gate_allows_excluded_params() {
    let mut env = Environment::with_prelude();
    // `a` here models a symbolic operand parameter (like the BV bridge's `a`/`b`)
    // — a quantified variable, NOT a soundness axiom. Excluding it must let an
    // otherwise-zero-trust theorem pass.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_str("True"),
    })
    .expect("register operand param");
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("usesParamA"),
        level_params: vec![],
        type_: Expr::const_str("True"),
        value: Expr::const_str("a"),
    })
    .expect("register theorem");

    // Without excluding `a`, the gate refuses.
    assert!(axiom_deps_subset_foundational(&env, "usesParamA", &[]).is_err());
    // Excluding `a` as a quantified param, it accepts.
    assert!(axiom_deps_subset_foundational(&env, "usesParamA", &["a"]).is_ok());
}

// ── GATE 5: non-vacuity ("drop a clause ⇒ must go SAT ⇒ refuse") ──────────────

/// `x ∧ ¬x` over one var: literals `0` (x), `1` (¬x). Each clause is a unit;
/// the conjunction is UNSAT, and dropping EITHER clause makes it SAT. Genuinely
/// non-vacuous — both clauses are load-bearing.
fn minimal_unsat_nonvacuous() -> CnfView {
    CnfView {
        clauses: vec![vec![0], vec![1]],
        num_vars: 1,
    }
}

#[test]
fn non_vacuity_accepts_a_genuine_minimal_refutation() {
    non_vacuity_check(&minimal_unsat_nonvacuous())
        .expect("minimal x ∧ ¬x is UNSAT and every clause is needed");
}

#[test]
fn non_vacuity_refuses_a_redundant_clause() {
    // x ∧ ¬x is already UNSAT; add a THIRD, redundant clause (y). Dropping the
    // redundant clause leaves the formula UNSAT ⇒ that clause is not needed ⇒
    // vacuous w.r.t. it. The gate must catch the redundant clause.
    let cnf = CnfView {
        clauses: vec![vec![0], vec![1], vec![2]], // x, ¬x, y
        num_vars: 2,
    };
    match non_vacuity_check(&cnf).unwrap_err() {
        BridgeError::Vacuous { clause } => {
            // Dropping clause 2 (the y unit) still leaves x ∧ ¬x UNSAT.
            assert_eq!(clause, 2, "the redundant y clause is the vacuous one");
        }
        other => panic!("expected Vacuous, got {other:?}"),
    }
}

#[test]
fn non_vacuity_refuses_a_sat_obligation_fail_closed() {
    // A SAT obligation has no refutation to be non-vacuous about — refuse.
    let cnf = CnfView {
        clauses: vec![vec![0]], // just x; trivially SAT
        num_vars: 1,
    };
    match non_vacuity_check(&cnf).unwrap_err() {
        BridgeError::NotProbeable(_) => {}
        other => panic!("expected NotProbeable, got {other:?}"),
    }
}

#[test]
fn non_vacuity_refuses_an_empty_obligation() {
    let cnf = CnfView {
        clauses: vec![],
        num_vars: 0,
    };
    assert!(matches!(
        non_vacuity_check(&cnf).unwrap_err(),
        BridgeError::NotProbeable(_)
    ));
}

// ── GATE 3: the meta-theorem TODO is a REFUSAL, not a silent pass ─────────────

#[test]
fn unimplemented_meta_theorem_fails_closed() {
    let meta = UnimplementedMeta {
        play: "D·XLATE".to_string(),
    };
    let mut env = Environment::with_prelude();
    let cert = ingest(good_envelope()).unwrap();
    match meta.discharge(&mut env, &cert).unwrap_err() {
        BridgeError::MetaUnimplemented(play) => assert_eq!(play, "D·XLATE"),
        other => panic!("expected MetaUnimplemented, got {other:?}"),
    }
}

// ── the full 5-gate pipeline, fail-closed end to end ─────────────────────────

#[test]
fn pipeline_aborts_at_ingest_on_a_forged_envelope() {
    let mut env = Environment::with_prelude();
    let meta = UnimplementedMeta {
        play: "D·XLATE".to_string(),
    };
    let cnf = minimal_unsat_nonvacuous();
    let mut forged = good_envelope();
    forged.witness.clear(); // forged: empty witness
    let inputs = PlayInputs {
        expected_hashes: &[hash(0xAB), hash(0xCD)],
        meta: &meta,
        allowed_params: &[],
        cnf: &cnf,
    };
    assert_eq!(
        run_pipeline(&mut env, forged, &inputs).unwrap_err(),
        BridgeError::EmptyWitness,
        "pipeline fails closed at gate 1"
    );
}

#[test]
fn pipeline_aborts_at_hash_pin_on_wrong_artifact() {
    let mut env = Environment::with_prelude();
    let meta = UnimplementedMeta {
        play: "D·XLATE".to_string(),
    };
    let cnf = minimal_unsat_nonvacuous();
    let inputs = PlayInputs {
        // Checker re-derived DIFFERENT source hashes ⇒ wrong artifact.
        expected_hashes: &[hash(0x11)],
        meta: &meta,
        allowed_params: &[],
        cnf: &cnf,
    };
    assert!(matches!(
        run_pipeline(&mut env, good_envelope(), &inputs).unwrap_err(),
        BridgeError::HashMismatch(_)
    ));
}

#[test]
fn pipeline_aborts_at_meta_theorem_when_unimplemented() {
    // Ingest + hash-pin pass; the UNIMPLEMENTED meta-theorem then fails closed —
    // a scaffold can never pass the pipeline as if it were a proof.
    let mut env = Environment::with_prelude();
    let meta = UnimplementedMeta {
        play: "D·XLATE".to_string(),
    };
    let cnf = minimal_unsat_nonvacuous();
    let inputs = PlayInputs {
        expected_hashes: &[hash(0xAB), hash(0xCD)],
        meta: &meta,
        allowed_params: &[],
        cnf: &cnf,
    };
    assert_eq!(
        run_pipeline(&mut env, good_envelope(), &inputs).unwrap_err(),
        BridgeError::MetaUnimplemented("D·XLATE".to_string()),
        "the typed-TODO meta-theorem refuses; pipeline fails closed at gate 3"
    );
}

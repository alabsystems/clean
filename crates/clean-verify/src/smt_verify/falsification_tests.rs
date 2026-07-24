// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Standing falsification suite for the SMT/Alethe proof checkers.
//!
//! Each fixture below is a *genuinely invalid* proof: a satisfiable premise set
//! from which the empty clause is derived only by laundering the **claimed**
//! (and false) clause of a structurally-accepted step — an unchecked theory
//! lemma (`bv`/`lra`/`lia`/`arrays`/`fp`) or a boolean-rule catch-all
//! (`contraction`/`and`/`or`/`true`) — into an otherwise honestly-recomputed
//! resolution.
//!
//! These reproduce root causes B and C from
//! `docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md`. The invariant this module
//! pins: **a "verified refutation / discharged obligation" verdict requires the
//! empty clause to be FULLY kernel-verified; a holey proof is never `valid` /
//! `CertificateVerdict::Valid` / `s VERIFIED` / a discharged contract.**
//!
//! Structure of each test:
//! - The raw `SmtVerifyResult.valid` **may** be `true` (it is the documented
//!   *structural* precondition "derives the empty clause") — that is fine.
//! - But `stats.is_fully_verified()` MUST be `false` (the step is a hole).
//! - Therefore every *consumer* that treats validity as a discharge
//!   (`CertificateVerdict`, `run_smtcomp` / SMT-COMP verdict, the ay contract's
//!   `fully_verified`) MUST report holey / not-verified / not-discharged.
//!
//! If a future change makes any of these pass as verified, that is a soundness
//! regression and this suite must fail.

use super::ay_smt_contract::{standard_full_contract, verify_ay_contract};
use super::certificate::{generate_certificate, CertificateVerdict};
use super::dag::{
    AletheRuleKind, SmtProofDag, SmtProofStep, SmtSort, SmtTerm, SmtTermId, SmtTheory,
    TheoryLemmaDetail,
};
use super::pipeline::{stats_to_verdict, SmtCompVerdict};
use super::{verify_smt_proof, VerifyMode};

/// Add a fresh Boolean variable term and return its id.
fn bool_var(dag: &mut SmtProofDag, name: &str) -> SmtTermId {
    dag.add_term(SmtTerm::Var(name.to_string(), SmtSort::Bool))
}

/// Assert the shared holey invariant for a proof that *structurally* derives the
/// empty clause but only through a structurally-accepted (unchecked) step.
///
/// This is the crux of the soundness fix: no consumer may treat such a proof as
/// a verified refutation.
fn assert_holey_not_verified(dag: &SmtProofDag, what: &str) {
    let result = verify_smt_proof(dag, VerifyMode::Permissive);

    // The raw structural bool may be true — that is the documented meaning of
    // `.valid` ("derives the empty clause"). What must NOT happen is the proof
    // being reported as *fully verified*.
    assert!(
        !result.stats.is_fully_verified(),
        "{what}: a laundered/holey proof must NOT be fully verified \
         (stats: {})",
        result.stats,
    );
    assert!(
        result.stats.structurally_accepted > 0,
        "{what}: the exploit must go through a structurally-accepted step \
         (stats: {})",
        result.stats,
    );

    // Consumer 1: the certificate verdict must be Holey, never Valid.
    let cert = generate_certificate(
        dag,
        &result,
        b"formula",
        b"proof",
        "smt_dag",
        VerifyMode::Permissive,
    );
    assert_ne!(
        cert.verdict,
        CertificateVerdict::Valid,
        "{what}: certificate must NOT be Valid for a holey proof",
    );
    assert_eq!(
        cert.verdict,
        CertificateVerdict::Holey,
        "{what}: certificate for a holey empty-clause proof must be Holey",
    );
    assert!(
        !cert.trust_summary.is_fully_verified(),
        "{what}: certificate trust summary must not report full verification",
    );

    // Consumer 2: the SMT-COMP verdict must be Holey, never Valid.
    let comp = stats_to_verdict(&result.stats, result.valid);
    assert_ne!(
        comp,
        SmtCompVerdict::Valid,
        "{what}: SMT-COMP verdict must NOT be valid for a holey proof",
    );
    assert_eq!(
        comp,
        SmtCompVerdict::Holey,
        "{what}: SMT-COMP verdict for a holey empty-clause proof must be holey",
    );

    // Consumer 3: the ay contract must not report the obligation discharged.
    let contract_result = verify_ay_contract(dag, &standard_full_contract());
    assert!(
        !contract_result.fully_verified,
        "{what}: ay contract must NOT mark a holey proof as fully verified",
    );
}

// ---------------------------------------------------------------------------
// Fixture 1: `contraction` fabricating the empty clause from a satisfiable
// premise. (root cause B, boolean-rule catch-all)
// ---------------------------------------------------------------------------

/// Assume the satisfiable unit `{p}`, then a `Contraction` step whose *claimed*
/// clause is empty. `contraction` is structurally accepted, so its false empty
/// clause is admitted verbatim and becomes the terminal empty clause.
fn build_contraction_fabricates_empty() -> SmtProofDag {
    let mut dag = SmtProofDag::new();
    let p = bool_var(&mut dag, "p");

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    // Contraction is a boolean rule -> structural_accept. Its claimed clause is
    // the empty clause, fabricated out of a single satisfiable premise.
    dag.add_step(SmtProofStep::Step {
        rule: AletheRuleKind::Contraction,
        clause: vec![],
        premises: vec![s0],
        args: vec![],
    });
    dag
}

#[test]
fn test_falsify_contraction_fabricates_empty_clause_is_holey() {
    let dag = build_contraction_fabricates_empty();
    assert_holey_not_verified(&dag, "contraction fabricating empty clause");
}

// ---------------------------------------------------------------------------
// Fixture 2: a `bv` theory lemma asserting a false clause, laundered to empty.
// (root cause B, unsupported/unparseable theory lemma)
// ---------------------------------------------------------------------------

/// Assume the satisfiable unit `{p}`, then a `bv` theory lemma whose clause is
/// `{¬p}` (no parseable BV constraints -> structurally accepted, admitting the
/// false unit `¬p`). Resolving `p` against the fabricated `¬p` derives empty.
fn build_bv_theory_lemma_launders_empty() -> SmtProofDag {
    let mut dag = SmtProofDag::new();
    let p = bool_var(&mut dag, "p");
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    // A BV theory lemma with a purely-Boolean clause is unparseable for the BV
    // checker -> structural_accept, admitting the *false* clause {¬p}.
    let s1 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Bv,
        kind: TheoryLemmaDetail::BvBitBlast {
            gate_type: None,
            width: None,
        },
        clause: vec![not_p],
    });
    // Honestly-recomputed resolution of {p} and {¬p} -> empty clause.
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });
    dag
}

#[test]
fn test_falsify_bv_theory_lemma_laundered_empty_is_holey() {
    let dag = build_bv_theory_lemma_launders_empty();
    assert_holey_not_verified(&dag, "bv theory-lemma laundering false clause");
}

// ---------------------------------------------------------------------------
// Fixture 3: an `arrays` extensionality lemma asserting a false clause.
// (root cause B, unsupported/unparseable theory lemma — arrays surface)
// ---------------------------------------------------------------------------

/// Same laundering as fixture 2 but through an arrays extensionality lemma with
/// a purely-Boolean clause, which the arrays checker cannot semantically verify.
fn build_arrays_lemma_launders_empty() -> SmtProofDag {
    let mut dag = SmtProofDag::new();
    let q = bool_var(&mut dag, "q");
    let not_q = dag.add_term(SmtTerm::Not(q));

    let s0 = dag.add_step(SmtProofStep::Assume(q));
    let s1 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Arrays,
        kind: TheoryLemmaDetail::ArrayExtensionality,
        clause: vec![not_q],
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(q),
    });
    dag
}

#[test]
fn test_falsify_arrays_lemma_laundered_empty_is_holey() {
    let dag = build_arrays_lemma_launders_empty();
    assert_holey_not_verified(&dag, "arrays extensionality laundering false clause");
}

// ---------------------------------------------------------------------------
// Fixture 4: the `and` / `true` boolean catch-all fabricating p and ¬p.
// (root cause B, boolean-rule catch-all)
// ---------------------------------------------------------------------------

/// No assumptions at all: two boolean-rule steps fabricate the contradictory
/// units `{p}` (via `True`) and `{¬p}` (via `AndPos`); both are structurally
/// accepted, then honestly resolved to the empty clause. The underlying formula
/// is trivially satisfiable (empty), so this is a genuine false refutation.
fn build_boolean_catchall_fabricates_contradiction() -> SmtProofDag {
    let mut dag = SmtProofDag::new();
    let p = bool_var(&mut dag, "p");
    let not_p = dag.add_term(SmtTerm::Not(p));

    // `True` boolean rule -> structural_accept; claimed clause {p}.
    let s0 = dag.add_step(SmtProofStep::Step {
        rule: AletheRuleKind::True,
        clause: vec![p],
        premises: vec![],
        args: vec![],
    });
    // `and`/AndPos boolean rule -> structural_accept; claimed clause {¬p}.
    let s1 = dag.add_step(SmtProofStep::Step {
        rule: AletheRuleKind::AndPos(0),
        clause: vec![not_p],
        premises: vec![],
        args: vec![],
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });
    dag
}

#[test]
fn test_falsify_boolean_catchall_fabricates_contradiction_is_holey() {
    let dag = build_boolean_catchall_fabricates_contradiction();
    assert_holey_not_verified(&dag, "and/true boolean catch-all fabricating p and ¬p");
}

// ---------------------------------------------------------------------------
// Correct-path guards: genuinely-VALID proofs must still report VERIFIED.
// These pin that the fix is fail-closed (only holey proofs change), not an
// over-tightening that rejects real refutations.
// ---------------------------------------------------------------------------

/// A genuinely-valid, fully kernel-verified refutation: assume p, assume ¬p,
/// resolve to the empty clause. Every step is axiomatic or kernel-verified.
fn build_genuinely_valid_refutation() -> SmtProofDag {
    let mut dag = SmtProofDag::new();
    let p = bool_var(&mut dag, "p");
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    let s1 = dag.add_step(SmtProofStep::Assume(not_p));
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });
    dag
}

#[test]
fn test_correct_path_valid_refutation_still_verifies() {
    let dag = build_genuinely_valid_refutation();
    let result = verify_smt_proof(&dag, VerifyMode::Permissive);

    assert!(
        result.valid,
        "genuine refutation must be structurally valid"
    );
    assert!(
        result.stats.is_fully_verified(),
        "genuine refutation must be fully kernel-verified (stats: {})",
        result.stats,
    );
    assert_eq!(result.stats.structurally_accepted, 0);

    // Certificate: Valid.
    let cert = generate_certificate(&dag, &result, b"f", b"p", "smt_dag", VerifyMode::Permissive);
    assert_eq!(
        cert.verdict,
        CertificateVerdict::Valid,
        "a fully-verified refutation must certify Valid",
    );
    assert!(cert.trust_summary.is_fully_verified());

    // SMT-COMP verdict: valid.
    assert_eq!(
        stats_to_verdict(&result.stats, result.valid),
        SmtCompVerdict::Valid,
        "a fully-verified refutation must have SMT-COMP verdict valid",
    );

    // ay contract: discharged.
    let contract_result = verify_ay_contract(&dag, &standard_full_contract());
    assert!(
        contract_result.fully_verified,
        "a fully-verified refutation must discharge the contract",
    );
}

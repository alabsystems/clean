// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn exact_v8_floor_matches_whether_the_actual_ordinary_authority_reaches_rejecting_kernel() {
    let (m, row, c) = fixture();
    assert!(observed(&m, &row, &c).0);
}
#[test]
fn wrong_certificate_obligation_short_circuits_before_any_lineage_child() {
    let (m, row, mut c) = fixture();
    c.obligation = ProofId::new(10);
    let (answer, _, end) = observed(&m, &row, &c);
    assert!(!answer);
    assert_eq!(end, 2);
}
#[test]
fn empty_clean_term_short_circuits_the_actual_nonempty_floor() {
    let (m, row, mut c) = fixture();
    if let ProofEvidence::CleanCic { term, .. } = &mut c.evidence {
        term.clear();
    }
    let (answer, _, end) = observed(&m, &row, &c);
    assert!(!answer);
    assert_eq!(end, 2);
}
#[test]
fn nonclean_evidence_never_reaches_lineage_or_kernel_even_with_matching_id() {
    let (m, row, mut c) = fixture();
    for e in [
        ProofEvidence::Trusted("audit".into()),
        ProofEvidence::LeanProof("opaque".into()),
        ProofEvidence::SmtProof(vec![1]),
        ProofEvidence::KaniHarness("h".into()),
        ProofEvidence::TranslationValidation {
            rule_name: "r".into(),
            smt_hash: [0; 32],
        },
    ] {
        c.evidence = e;
        assert!(!observed(&m, &row, &c).0);
    }
}
#[test]
fn legacy_index_identity_can_match_even_when_actual_module_owner_is_missing() {
    let (mut m, row, mut c) = fixture();
    m.functions.clear();
    if let ProofEvidence::CleanCic { lineage, .. } = &mut c.evidence {
        *lineage = crate::proof::clean_cic_lineage_digest(&row);
    }
    assert!(observed(&m, &row, &c).0);
}
#[test]
fn v8_symbol_identity_refuses_missing_owner_and_retains_first_physical_duplicate() {
    let (mut m, row, c) = fixture();
    m.functions.push(Function::new(
        FuncId::new(77),
        "ignored duplicate",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    assert!(observed(&m, &row, &c).0);
    m.functions.clear();
    assert!(!observed(&m, &row, &c).0);
}
#[test]
fn every_public_status_and_prover_spelling_is_ignored_by_only_this_identity_floor() {
    let (m, mut row, mut c) = fixture();
    for status in [
        ProofStatus::Pending,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Discharged,
        ProofStatus::Certified,
    ] {
        row.status = status;
        c.prover = "NOT a kernel name λ\0".into();
        assert!(observed(&m, &row, &c).0);
    }
}
#[test]
fn lineage_mismatch_is_false_without_any_kernel_verdict_or_fallback() {
    let (m, row, mut c) = fixture();
    if let ProofEvidence::CleanCic { lineage, .. } = &mut c.evidence {
        *lineage = ProofDigest::sha256([88; 32]);
    }
    assert!(!observed(&m, &row, &c).0);
}

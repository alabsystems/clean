// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn all_three_actual_request_families_match_actual_whole_prefix_projection() {
    parity(&fixture());
}
#[test]
fn duplicate_request_ids_across_variants_keep_every_repeat_after_first() {
    let mut b = fixture();
    for r in &mut b.requests {
        match r {
            NativeVerificationRequest::TrustVc(r) => r.id = NativeRequestId::new(77),
            NativeVerificationRequest::TrustMc(r) => r.id = NativeRequestId::new(77),
            NativeVerificationRequest::TrustWp(r) => r.id = NativeRequestId::new(77),
        }
    }
    let rows = parity(&b);
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::DuplicateRequestId(_)))
            .count(),
        2
    );
}
#[test]
fn actual_physical_request_index_is_bound_and_out_of_range_is_typed_refusal() {
    let b = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for index in [b.requests.len(), usize::MAX] {
        assert_eq!(
            b.request_metadata_errors_observed(index, &mut s, site()),
            Err(ObservedValueError::InvalidRange)
        );
    }
    assert!(s.first_refusal().is_none());
}
#[test]
fn empty_obligations_and_roots_precede_diagnostics_and_identity_children() {
    let mut b = bad();
    ids(&mut b.requests[1]).clear();
    let rows = parity(&b);
    let at = rows
        .iter()
        .position(|e| matches!(e, E::DuplicateRequestId(_)))
        .unwrap();
    assert!(matches!(&rows[at + 1], E::EmptyRequestObligations(_)));
    assert!(matches!(&rows[at + 2], E::EmptyLineageRoots(_)));
    assert!(matches!(
        &rows[at + 3],
        E::InvalidDiagnosticsPolicy {
            field: "include_source_spans",
            ..
        }
    ));
}
#[test]
fn wrong_declared_suite_precedes_tool_basic_then_expected_family_errors() {
    let b = bad();
    let rows = parity(&b);
    let suite = rows
        .iter()
        .position(|e| matches!(e, E::VerifierSuiteMismatch { .. }))
        .unwrap();
    assert!(matches!(
        rows[suite + 1],
        E::InvalidToolIdentityField {
            field: "request.provenance.expected_verifier",
            component: "version"
        }
    ));
    assert!(matches!(
        rows[suite + 2],
        E::ExpectedVerifierIdentityMismatch { .. }
    ));
}
#[test]
fn solver_empty_list_and_each_physical_blank_solver_have_distinct_original_counts() {
    let mut b = fixture();
    provenance(&mut b.requests[1]).solvers.clear();
    assert_eq!(
        parity(&b)
            .iter()
            .filter(|e| matches!(e, E::EmptyProvenanceField("request.provenance.solvers")))
            .count(),
        1
    );
    provenance(&mut b.requests[1]).solvers = vec![NativeToolIdentity::new(" "); 3];
    assert_eq!(
        parity(&b)
            .iter()
            .filter(|e| matches!(e, E::EmptyProvenanceField("request.provenance.solvers")))
            .count(),
        3
    );
}
#[test]
fn absent_replay_and_present_missing_transcript_are_not_collapsed() {
    let mut b = fixture();
    provenance(&mut b.requests[1]).replay = None;
    assert!(
        parity(&b)
            .iter()
            .any(|e| matches!(e, E::MissingReplayIdentity(_)))
    );
    provenance(&mut b.requests[1]).replay = Some(ProofReplayIdentity::new("trust_mc", "invoke"));
    assert!(
        parity(&b)
            .iter()
            .any(|e| matches!(e, E::MissingReplayTranscriptDigest(_)))
    );
}
#[test]
fn every_physical_duplicate_and_unknown_obligation_retains_original_order() {
    let mut b = fixture();
    *ids(&mut b.requests[1]) = vec![
        ProofId::new(99),
        ProofId::new(99),
        ProofId::new(1),
        ProofId::new(1),
    ];
    let rows = parity(&b);
    let selected: Vec<_> = rows
        .iter()
        .filter(|e| {
            matches!(
                e,
                E::UnknownRequestObligation { .. } | E::DuplicateRequestObligation { .. }
            )
        })
        .collect();
    assert!(matches!(
        selected.as_slice(),
        [
            E::UnknownRequestObligation { .. },
            E::DuplicateRequestObligation { .. },
            E::UnknownRequestObligation { .. },
            E::DuplicateRequestObligation { .. }
        ]
    ));
}
#[test]
fn known_obligation_id_duplicates_are_presence_only_without_status_authority() {
    let mut b = fixture();
    let mut duplicate = b.module.proof_obligations[0].clone();
    duplicate.status = ProofStatus::Pending;
    b.module.proof_obligations.push(duplicate);
    parity(&b);
}
#[test]
fn replay_context_errors_follow_all_physical_obligation_errors() {
    let b = bad();
    let rows = parity(&b);
    let last = rows
        .iter()
        .rposition(|e| {
            matches!(
                e,
                E::UnknownRequestObligation { .. } | E::DuplicateRequestObligation { .. }
            )
        })
        .unwrap();
    assert!(matches!(
        rows[last + 1],
        E::UnsupportedNativeRequestMode { .. }
    ));
    assert!(rows[last + 2..].iter().any(|e| matches!(
        e,
        E::InvalidReplayAtom {
            field: "formula.smtlib",
            ..
        }
    )));
}
#[test]
fn valid_atom_runs_actual_payload_digest_and_predicate_child() {
    let mut b = fixture();
    let mut atom = NativeReplayAtom::assumption(
        NativeReplayAtomId::new(0),
        ProofFormula::smtlib2("true", "Bool"),
    );
    atom.obligation = Some(ProofId::new(1));
    provenance(&mut b.requests[1]).replay_context.atoms = vec![atom];
    parity(&b);
    let (_, o, _) = observed(&b, 1);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
}
#[test]
fn long_unicode_tool_mismatch_names_are_owned_whole_and_outlive_source() {
    let mut b = fixture();
    provenance(&mut b.requests[1]).expected_verifier.name = "wrong λ\0尾".repeat(700);
    let expected = parity(&b);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_metadata_errors_observed(1, &mut s, site())
        .unwrap();
    drop(b);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn irrelevant_lineage_function_and_certificate_fields_do_not_enter_prefix() {
    let b = fixture();
    let (rows, a, end) = observed(&b, 1);
    let mut changed = b.clone();
    changed.lineage.nodes.clear();
    changed.lineage.roots.clear();
    if let NativeVerificationRequest::TrustMc(r) = &mut changed.requests[1] {
        r.function = FuncId::new(u32::MAX);
    }
    let (new, c, end_c) = observed(&changed, 1);
    assert_eq!(rows, new);
    assert_eq!(&a.events[..end], &c.events[..end_c]);
}
#[test]
fn metadata_success_does_not_replace_source_certificate_or_whole_request_validation() {
    let mut b = fixture();
    b.lineage.nodes.clear();
    let rows = parity(&b);
    assert!(rows.is_empty());
    assert!(b.validate().is_err());
}

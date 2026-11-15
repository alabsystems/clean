// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::chunks_exact_to_as_chunks,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_three_actual_request_families_preserve_whole_original_group() {
    let (b, _) = fixture();
    for r in &b.requests {
        observed(&b, r);
    }
    let (_, r) = fixture();
    observed(&b, &r);
}
#[test]
fn every_physical_root_repeat_unknown_and_target_error_keeps_original_order() {
    let (b, r) = bad();
    let rows = observed(&b, &r).0;
    assert!(matches!(
        &rows[0],
        E::RequestLineageRootTargetMismatch { .. }
    ));
    assert!(matches!(&rows[1], E::UnknownLineageRoot { .. }));
    assert!(matches!(&rows[2], E::DuplicateRequestLineageRoot { .. }));
    assert!(matches!(
        &rows[3],
        E::RequestLineageRootTargetMismatch { .. }
    ));
    assert!(matches!(
        &rows[4],
        E::RequestSourceDigestNotInLineage { .. }
    ));
}
#[test]
fn last_physical_duplicate_root_node_controls_target_even_if_earlier_exact() {
    let (mut b, r) = fixture();
    let mut wrong = b.lineage.nodes[0].clone();
    wrong.target_module = ProofDigest::sha256([8; 32]);
    b.lineage.nodes.push(wrong);
    assert!(
        observed(&b, &r)
            .0
            .iter()
            .any(|e| matches!(e, E::RequestLineageRootTargetMismatch { .. }))
    );
    let exact = b.lineage.nodes[0].clone();
    b.lineage.nodes.push(exact);
    assert!(
        !observed(&b, &r)
            .0
            .iter()
            .any(|e| matches!(e, E::RequestLineageRootTargetMismatch { .. }))
    );
}
#[test]
fn unknown_manifest_root_and_absent_actual_node_are_independent_checks() {
    let (mut b, mut r) = fixture();
    let known = roots(&mut r)[0];
    b.lineage.roots.clear();
    assert!(
        observed(&b, &r)
            .0
            .iter()
            .any(|e| matches!(e, E::UnknownLineageRoot { .. }))
    );
    b.lineage.roots.push(known);
    b.lineage.nodes.clear();
    let rows = observed(&b, &r).0;
    assert!(!rows.iter().any(|e| matches!(
        e,
        E::UnknownLineageRoot { .. } | E::RequestLineageRootTargetMismatch { .. }
    )));
}
#[test]
fn original_adapter_input_source_not_provenance_label_drives_binding() {
    let (mut b, r) = fixture();
    let baseline = observed(&b, &r).0;
    b.provenance.source_digest = Some(ProofDigest::sha256([8; 32]));
    assert_eq!(observed(&b, &r).0, baseline);
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest::sha256([9; 32]),
    };
    assert!(
        observed(&b, &r)
            .0
            .iter()
            .any(|e| matches!(e, E::RequestSourceDigestNotInLineage { .. }))
    );
}
#[test]
fn no_adapter_source_keeps_original_none_filter_and_skips_source_error() {
    let (mut b, r) = bad();
    b.input = NativeAdapterInput::TrustIrModule;
    let rows = observed(&b, &r).0;
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::RequestSourceDigestNotInLineage { .. }))
    );
}
#[test]
fn request_obligation_errors_are_unique_unsigned_ascending_then_function_checks() {
    let (b, r) = bad();
    let rows = observed(&b, &r).0;
    let ids: Vec<_> = rows
        .iter()
        .filter_map(|e| match e {
            E::RequestObligationNotInLineage { obligation, .. } => Some(obligation.index()),
            _ => None,
        })
        .collect();
    assert_eq!(ids, vec![0, 1, 77]);
    let missing = rows
        .iter()
        .position(|e| matches!(e, E::MissingFunction { .. }))
        .unwrap();
    assert!(
        rows[..missing]
            .iter()
            .any(|e| matches!(e, E::MissingObligationSourceSpan { .. }))
    );
    assert!(
        rows[missing + 1..]
            .iter()
            .all(|e| matches!(e, E::RequestObligationFunctionMismatch { .. }))
    );
}
#[test]
fn first_physical_sidecar_row_wins_over_later_exact_or_missing_fields() {
    let (mut b, r) = fixture();
    let mut first = b.compiler_facts.obligation_sources[0].clone();
    first.span = None;
    first.assertion_id = None;
    first.function = None;
    b.compiler_facts.obligation_sources.insert(0, first);
    let a = observed(&b, &r).0;
    assert!(
        a.iter()
            .any(|e| matches!(e, E::MissingObligationSourceSpan { .. }))
    );
    b.compiler_facts.obligation_sources.swap(0, 1);
    assert!(
        !observed(&b, &r)
            .0
            .iter()
            .any(|e| matches!(e, E::MissingObligationSourceSpan { .. }))
    );
}
#[test]
fn absent_sidecar_skips_only_span_assertion_and_function_mismatch() {
    let (mut b, r) = fixture();
    b.compiler_facts.obligation_sources.clear();
    let rows = observed(&b, &r).0;
    assert!(!rows.iter().any(|e| matches!(
        e,
        E::MissingObligationSourceSpan { .. }
            | E::MissingObligationSourceAssertion { .. }
            | E::RequestObligationFunctionMismatch { .. }
    )));
}
#[test]
fn span_then_assertion_missing_errors_are_separate_for_each_sorted_obligation() {
    let (mut b, r) = fixture();
    for s in &mut b.compiler_facts.obligation_sources {
        s.span = None;
        s.assertion_id = None;
    }
    let rows = observed(&b, &r).0;
    let selected: Vec<_> = rows
        .iter()
        .filter(|e| {
            matches!(
                e,
                E::MissingObligationSourceSpan { .. } | E::MissingObligationSourceAssertion { .. }
            )
        })
        .collect();
    for pair in selected.chunks_exact(2) {
        assert!(matches!(
            pair,
            [
                E::MissingObligationSourceSpan { .. },
                E::MissingObligationSourceAssertion { .. }
            ]
        ));
    }
}
#[test]
fn present_indexed_function_and_sparse_fallback_function_both_match_actual_getter() {
    let (mut b, mut r) = fixture();
    observed(&b, &r);
    let sparse = FuncId::new(909);
    b.module.functions[0].id = sparse;
    function(&mut r, Some(sparse));
    for s in &mut b.compiler_facts.obligation_sources {
        s.function = Some(sparse);
    }
    assert!(!observed(&b, &r).0.iter().any(|e| matches!(
        e,
        E::MissingFunction { .. } | E::RequestObligationFunctionMismatch { .. }
    )));
}
#[test]
fn indexed_slot_id_mismatch_does_not_hide_a_later_matching_function() {
    let (mut b, mut r) = fixture();
    let mut found = b.module.functions[0].clone();
    found.id = FuncId::new(0);
    b.module.functions[0].id = FuncId::new(8);
    b.module.functions.push(found);
    function(&mut r, Some(FuncId::new(0)));
    assert!(
        !observed(&b, &r)
            .0
            .iter()
            .any(|e| matches!(e, E::MissingFunction { .. }))
    );
}
#[test]
fn absent_function_is_reported_before_actual_sidecar_function_mismatches() {
    let (b, r) = bad();
    let rows = observed(&b, &r).0;
    let pos = rows
        .iter()
        .position(|e| matches!(e, E::MissingFunction { .. }))
        .unwrap();
    assert!(
        rows[pos + 1..]
            .iter()
            .any(|e| matches!(e, E::RequestObligationFunctionMismatch { actual: None, .. }))
    );
}
#[test]
fn functionless_vc_skips_function_binding_without_dropping_lineage_checks() {
    let (mut b, _) = fixture();
    let mut r = b.requests.remove(0);
    function(&mut r, None);
    let rows = observed(&b, &r).0;
    assert!(!rows.iter().any(|e| matches!(
        e,
        E::MissingFunction { .. } | E::RequestObligationFunctionMismatch { .. }
    )));
}
#[test]
fn source_group_does_not_replace_duplicate_known_obligation_or_certificate_checks() {
    let (b, mut r) = fixture();
    *ids(&mut r) = vec![ProofId::new(1), ProofId::new(1)];
    let rows = observed(&b, &r).0;
    assert!(rows.iter().all(selected));
    let mut whole = b.clone();
    whole.requests = vec![r];
    assert!(
        whole
            .request_errors_original_for_observed_tests()
            .iter()
            .any(|e| matches!(e, E::DuplicateRequestObligation { .. }))
    );
}
#[test]
fn unrelated_request_provenance_does_not_change_source_group_output_or_events() {
    let (b, r) = fixture();
    let (rows, a, end) = observed(&b, &r);
    let mut changed = r.clone();
    match &mut changed {
        NativeVerificationRequest::TrustVc(r) => {
            r.provenance.expected_verifier.name = "x".repeat(7000)
        }
        NativeVerificationRequest::TrustMc(r) => {
            r.provenance.expected_verifier.name = "x".repeat(7000)
        }
        NativeVerificationRequest::TrustWp(r) => {
            r.provenance.expected_verifier.name = "x".repeat(7000)
        }
    }
    let (new, c, end_c) = observed(&b, &changed);
    assert_eq!(rows, new);
    assert_eq!(&a.events[..end], &c.events[..end_c]);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn empty_requested_roots_ignore_manifest_roots_and_have_empty_sets() {
    let mut i = fixture();
    i.roots.clear();
    observed(&i);
    assert!(expected(&i).0.0.is_empty());
}
#[test]
fn missing_root_and_missing_dependency_keep_actual_known_reachable_members() {
    let mut i = fixture();
    i.roots.push(ProofLineageId::new(u32::MAX));
    observed(&i);
}
#[test]
fn self_and_mutual_cycles_terminate_with_exact_seen_union() {
    let mut i = fixture();
    i.manifest.nodes[2].depends_on = vec![ProofLineageId::new(2)];
    observed(&i);
}
#[test]
fn last_physical_duplicate_node_wins_including_its_edges() {
    let mut i = fixture();
    let mut replacement = node(0, 8);
    replacement.obligations = vec![ProofId::new(80)];
    replacement.depends_on = vec![ProofLineageId::new(2)];
    i.manifest.nodes.push(replacement);
    observed(&i);
    let old = expected(&i);
    assert!(!old.0.0.contains(&ProofId::new(0)));
    assert!(!old.0.0.contains(&ProofId::new(1)));
    assert!(old.0.0.contains(&ProofId::new(80)));
}
#[test]
fn full_root_and_dependency_stack_order_never_changes_set_semantics() {
    let mut i = fixture();
    for roots in [vec![0, 2], vec![2, 0], vec![0, 2, 0]] {
        i.roots = roots.into_iter().map(ProofLineageId::new).collect();
        observed(&i);
    }
}
#[test]
fn duplicate_obligations_and_equal_full_certificates_deduplicate_only_as_raw_sets() {
    let mut i = fixture();
    let n = &mut i.manifest.nodes[0];
    n.obligations = vec![ProofId::new(9), ProofId::new(9), ProofId::new(0)];
    let c = certificate(9, "same", 4);
    n.certificates = vec![
        c.clone(),
        c.clone(),
        certificate(9, "same", 5),
        certificate(9, "different", 4),
    ];
    observed(&i);
}
#[test]
fn unreachable_nodes_do_not_contribute_even_with_matching_source() {
    let mut i = fixture();
    i.manifest.nodes.push(node(44, 2));
    observed(&i);
    assert!(!expected(&i).0.0.contains(&ProofId::new(44)));
}
#[test]
fn absent_source_filter_admits_every_complete_root_closure() {
    let mut i = fixture();
    i.source = None;
    observed(&i);
    let old = expected(&i);
    assert_eq!(old.0.0, old.1.0);
    assert_eq!(old.0.1, old.1.1);
}
#[test]
fn source_filter_can_match_any_transitive_source_not_only_root_source() {
    let i = fixture();
    observed(&i);
    let old = expected(&i);
    assert!(old.1.0.contains(&ProofId::new(0)));
    assert!(old.1.0.contains(&ProofId::new(1)));
    assert!(!old.1.0.contains(&ProofId::new(2)));
}
#[test]
fn a_matching_source_from_another_root_does_not_leak_membership() {
    let mut i = fixture();
    i.source = Some(digest(3));
    observed(&i);
    let old = expected(&i);
    assert_eq!(old.1.0, [ProofId::new(2)].into_iter().collect());
}
#[test]
fn repeated_physical_roots_still_recompute_and_union_exact_members() {
    let mut i = fixture();
    i.roots = vec![ProofLineageId::new(0); 5];
    observed(&i);
}
#[test]
fn raw_digest_algorithm_is_part_of_membership_and_zero_is_not_validated_here() {
    let mut i = fixture();
    i.source = Some(ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [2; 32],
    });
    observed(&i);
    assert!(expected(&i).1.0.is_empty());
    i.manifest.nodes[1].source_module = i.source.unwrap();
    observed(&i);
    i.source = Some(ProofDigest::sha256([0; 32]));
    i.manifest.nodes[1].source_module = i.source.unwrap();
    observed(&i);
    assert!(!expected(&i).1.0.is_empty());
}
#[test]
fn raw_prover_bytes_are_not_normalized_or_collapsed_by_obligation() {
    let mut i = fixture();
    i.manifest.nodes[0].certificates = ["TRUST-VC", "trust_vc", "λ\0尾", "é", "e\u{301}"]
        .into_iter()
        .map(|s| certificate(0, s, 1))
        .collect();
    observed(&i);
    assert_eq!(expected(&i).0.1.len(), 7);
}
#[test]
fn long_same_length_provers_differing_only_at_last_byte_remain_distinct() {
    let mut i = fixture();
    let a = "λ".repeat(1600) + "a";
    let b = "λ".repeat(1600) + "b";
    i.manifest.nodes[0].certificates = vec![certificate(0, &a, 1), certificate(0, &b, 1)];
    observed(&i);
}
#[test]
fn all_public_observed_membership_queries_match_original_sets_and_refuse_false_publication() {
    let i = fixture();
    let old = expected(&i);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = i
        .manifest
        .request_lineage_observed(&i.roots, i.source, &mut s, site())
        .unwrap();
    for id in 0..5 {
        assert_eq!(
            out.source_bound_obligation_contains_observed(ProofId::new(id), &mut s, site())
                .unwrap(),
            old.1.0.contains(&ProofId::new(id))
        );
        assert_eq!(
            out.reachable_source_contains_observed(&digest(id as u8), &mut s, site())
                .unwrap(),
            old.0.2.contains(&digest(id as u8))
        );
    }
    for r in &i.manifest.nodes[0].certificates {
        assert_eq!(
            out.source_bound_certificate_contains_observed(r, &mut s, site())
                .unwrap(),
            old.1.1.contains(r)
        );
    }
    out.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let out = NativeRequestLineage::default();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    assert!(
        !out.source_bound_obligation_contains_observed(ProofId::new(99), &mut s, site())
            .unwrap()
    );
    drop(s);
    let mut o = Observer {
        stop: Some(base.events.len()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        out.source_bound_obligation_contains_observed(ProofId::new(99), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    out.retire_observed(&mut s, site()).unwrap_err();
}
#[test]
fn data_closure_does_not_validate_schema_target_cycles_or_certificates() {
    let mut i = fixture();
    i.manifest.schema_version = 0;
    i.manifest.nodes[0].target_module = digest(0);
    i.manifest.nodes[0].certificates[0].prover.clear();
    i.manifest.nodes[0].certificates[0].evidence_digest = digest(0);
    observed(&i);
    assert!(i.manifest.validate().is_err());
}

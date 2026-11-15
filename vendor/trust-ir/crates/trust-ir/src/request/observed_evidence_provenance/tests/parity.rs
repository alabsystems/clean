// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn all_three_original_mismatches_keep_exact_order_and_request_id() {
    let (r, e) = bad();
    let (rows, _, _) = observed(&r, &e);
    assert_eq!(
        rows,
        ["verifier", "solvers", "replay"]
            .into_iter()
            .map(|field| E::EvidenceProvenanceMismatch {
                request: r.id(),
                field
            })
            .collect::<Vec<_>>()
    );
}
#[test]
fn reordered_solver_multiset_is_accepted_with_duplicate_counts_preserved() {
    let (mut r, mut e) = matched();
    let a = NativeToolIdentity::new("a");
    let b = NativeToolIdentity::new("b");
    provenance(&mut r).solvers = vec![a.clone(), b.clone(), a.clone()];
    payload(&mut e).solvers = vec![b, a.clone(), a];
    assert!(observed(&r, &e).0.is_empty());
}
#[test]
fn same_distinct_solver_set_and_length_with_different_counts_is_refused() {
    let (mut r, mut e) = matched();
    let a = NativeToolIdentity::new("a");
    let b = NativeToolIdentity::new("b");
    provenance(&mut r).solvers = vec![a.clone(), a.clone(), b.clone()];
    payload(&mut e).solvers = vec![a, b.clone(), b];
    assert_eq!(
        observed(&r, &e).0,
        vec![E::EvidenceProvenanceMismatch {
            request: r.id(),
            field: "solvers"
        }]
    );
}
#[test]
fn raw_canonical_aliases_do_not_match_verifier_or_solver_records() {
    let (mut r, mut e) = matched();
    provenance(&mut r).expected_verifier = NativeToolIdentity::new("TrustMC");
    payload(&mut e).verifier = NativeToolIdentity::new("trust_mc");
    provenance(&mut r).solvers = vec![NativeToolIdentity::new("AY")];
    payload(&mut e).solvers = vec![NativeToolIdentity::new("ay")];
    assert_eq!(observed(&r, &e).0.len(), 2);
}
#[test]
fn optional_raw_fields_and_digest_bytes_remain_part_of_solver_equality() {
    let (mut r, mut e) = matched();
    let a = NativeToolIdentity::new("solver");
    let mut b = a.clone();
    b.version = Some("".into());
    provenance(&mut r).solvers = vec![a];
    payload(&mut e).solvers = vec![b];
    assert_eq!(observed(&r, &e).0.len(), 1);
}
#[test]
fn missing_expected_replay_skips_even_a_different_recorded_evidence_replay() {
    let (mut r, mut e) = matched();
    provenance(&mut r).replay = None;
    payload(&mut e).replay = ProofReplayIdentity::new("garbage", "");
    assert!(observed(&r, &e).0.is_empty());
}
#[test]
fn optional_expected_replay_compares_every_raw_field() {
    let (r, e) = matched();
    for field in [0, 1, 2] {
        let mut e = e.clone();
        let p = &mut payload(&mut e).replay;
        match field {
            0 => p.engine.push('x'),
            1 => p.invocation.push('x'),
            _ => p.transcript_digest = None,
        }
        assert_eq!(observed(&r, &e).0.len(), 1);
    }
}
#[test]
fn empty_and_unequal_length_solver_lists_match_the_original() {
    for (a, b) in [(0, 0), (0, 2), (2, 0), (2, 3)] {
        let (mut r, mut e) = matched();
        provenance(&mut r).solvers = vec![NativeToolIdentity::new("same"); a];
        payload(&mut e).solvers = vec![NativeToolIdentity::new("same"); b];
        observed(&r, &e);
    }
}
#[test]
fn long_same_length_last_byte_difference_is_not_a_membership_match() {
    let (mut r, mut e) = matched();
    let a = NativeToolIdentity::new("λ🦀".repeat(800) + "a");
    let b = NativeToolIdentity::new("λ🦀".repeat(800) + "b");
    provenance(&mut r).solvers = vec![a];
    payload(&mut e).solvers = vec![b];
    assert_eq!(observed(&r, &e).0.len(), 1);
}
#[test]
fn all_three_actual_request_provenance_getters_are_used_faithfully() {
    let requests = crate::request::tests::native_bundle().requests;
    assert_eq!(requests.len(), 3);
    for r in requests {
        let (_, mut e) = matched();
        let b = payload(&mut e);
        b.verifier = r.expected_verifier_identity().clone();
        b.solvers = r.solver_identities().to_vec();
        if let Some(p) = r.provenance().replay_identity() {
            b.replay = p.clone();
        }
        assert!(observed(&r, &e).0.is_empty());
    }
}
#[test]
fn binding_helper_does_not_substitute_request_id_or_digest_validation() {
    let (r, mut e) = matched();
    payload(&mut e).request = NativeRequestId::new(999);
    payload(&mut e).request_digest = ProofDigest::sha256([99; 32]);
    assert!(observed(&r, &e).0.is_empty());
}
#[test]
fn whole_returned_mismatches_outlive_both_original_inputs() {
    let (r, e) = bad();
    let expected = ordinary(&r, &e);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e
        .provenance_binding_errors_observed(&r, &mut s, site())
        .unwrap();
    drop(r);
    drop(e);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}

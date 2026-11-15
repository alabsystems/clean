// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn real_existing_sealed_authority_matches_exact_original_true_query() {
    let (a, b) = minted();
    assert!(observed(&a, &b).0);
}
#[test]
fn content_equal_clone_has_no_live_identity_and_is_refused_before_hashing() {
    let (a, b) = minted();
    let clone = b.clone();
    assert_eq!(b, clone);
    assert!(!observed(&a, &clone).0);
}
#[test]
fn independently_minted_equal_content_has_a_distinct_private_nonce() {
    let (a, b) = minted();
    let (other, c) = minted();
    assert_eq!(b, c);
    assert!(!observed(&a, &c).0);
    assert!(observed(&other, &c).0);
}
#[test]
fn same_nonce_but_changed_whole_bundle_preimage_is_false_before_validation() {
    let (a, mut b) = minted();
    b.provenance.producer_version.push_str("-different");
    assert_ne!(a.bundle_digest, b.stable_digest());
    assert!(!observed(&a, &b).0);
}
#[test]
fn equal_private_nonce_and_equal_bundle_digest_still_require_full_actual_validation() {
    let (a, b) = tampered();
    assert!(b.source_generation_live.matches(&a.nonce));
    assert_eq!(a.bundle_digest, b.stable_digest());
    assert!(!observed(&a, &b).0);
}
#[test]
fn no_live_nonce_short_circuits_even_an_unencodable_or_malformed_bundle() {
    let (a, b) = minted();
    let mut clone = b.clone();
    clone.module.types.push(crate::Ty::Error);
    clone.schema_version = 0;
    let (answer, o, end) = observed(&a, &clone);
    assert!(!answer);
    assert!(end < 20);
    assert!(o.events[..end].iter().all(|p| p.work < 100));
}
#[test]
fn existing_capability_and_source_are_never_mutated_or_reminted_by_query() {
    let (a, b) = minted();
    let before = b.clone();
    let nonce = super::super::super::Arc::as_ptr(&a.nonce);
    let digest = a.bundle_digest;
    assert!(observed(&a, &b).0);
    assert!(observed(&a, &b).0);
    assert_eq!(b, before);
    assert_eq!(nonce, super::super::super::Arc::as_ptr(&a.nonce));
    assert_eq!(digest, a.bundle_digest);
}
#[test]
fn exact_raw_provenance_tail_difference_is_bound_by_the_actual_canonical_digest() {
    let (a, mut b) = minted();
    b.provenance.source_artifact = Some("whole λ\0尾".repeat(400));
    assert!(!observed(&a, &b).0);
    assert_ne!(a.bundle_digest, b.stable_digest());
}
#[test]
fn independent_digest_and_full_validation_are_both_reached_only_after_identity() {
    let (a, b) = minted();
    let (_, full, full_end) = observed(&a, &b);
    let mut changed = b.clone();
    let (_, short, short_end) = observed(&a, &changed);
    assert!(full_end > short_end);
    changed.schema_version = 0;
    assert!(!observed(&a, &changed).0);
    assert!(full.events.iter().any(|p| p.work >= 100));
    assert!(!short.events.is_empty());
}
#[test]
fn original_zero_instruction_fuel_is_preserved_for_true_and_false_queries() {
    let (a, b) = minted();
    for source in [&b, &b.clone()] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        assert_eq!(
            a.authorizes_bundle_kernel_less_observed(source, &mut s, site())
                .unwrap(),
            a.authorizes_bundle(source)
        );
        assert_eq!(s.remaining_fuel(), 0);
    }
}

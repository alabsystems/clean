// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_owned_bundle_string_family_is_consumed_without_validation_or_authority() {
    let rows = strings();
    assert_eq!(rows.len(), 17);
    let observed = capture(rows);
    assert!(observed.events.len() > 70);
    assert!(
        observed.events[..observed.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn nested_lineage_errors_and_both_owned_formula_locations_drain() {
    let mut rows = vec![E::Lineage(lineage())];
    rows.extend(sites());
    let observed = capture(rows);
    // Four nested provers plus four actual formula labels retain spare capacity.
    assert_eq!(
        observed
            .events
            .iter()
            .filter(|p| p.copy_bytes == 8193)
            .count(),
        8
    );
}
#[test]
fn every_language_and_full_other_producer_are_retired() {
    let observed = capture(collections());
    assert_eq!(
        observed
            .events
            .iter()
            .filter(|p| p.copy_bytes == 8193)
            .count(),
        7
    );
    assert!(
        observed
            .events
            .iter()
            .any(|p| p.work == 6 * (11 + 12 + 8) + 4)
    );
}
#[test]
fn single_error_and_batch_share_the_same_payload_cleanup() {
    let request = NativeRequestId::new(4);
    let mut one = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut one);
    E::DuplicateEvidenceArtifact {
        request,
        name: label(),
    }
    .retire_observed(&mut s, site())
    .unwrap();
    let batch = capture(vec![E::DuplicateEvidenceArtifact {
        request,
        name: label(),
    }]);
    assert_eq!(
        one.events.iter().filter(|p| p.copy_bytes == 8193).count(),
        1
    );
    assert_eq!(
        batch.events.iter().filter(|p| p.copy_bytes == 8193).count(),
        1
    );
    assert!(batch.bytes > one.bytes);
}
#[test]
fn genuine_ordinary_validation_errors_are_disposable_without_changing_source() {
    use crate::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
    let digest = crate::ProofDigest::sha256_domain("retirement-fixture", b"source");
    let bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: digest,
        },
        digest,
        crate::Module::new("unchanged"),
        crate::ProofLineageManifest::new(),
    );
    let before = bundle.validate().unwrap_err();
    let text: Vec<_> = before.iter().map(ToString::to_string).collect();
    capture(before);
    assert_eq!(
        bundle
            .validate()
            .unwrap_err()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        text
    );
    assert_eq!(bundle.module.name, "unchanged");
}
#[test]
fn empty_and_spare_capacity_batches_keep_terminal_publication_and_zero_fuel() {
    for rows in [Vec::new(), Vec::with_capacity(121)] {
        let observed = capture(rows);
        assert!(
            observed
                .events
                .iter()
                .any(|p| p.copy_bytes == 121 * size_of::<E>())
                || observed.bytes < 121 * size_of::<E>()
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn valid_live_fixture_issues_exact_digest_and_installs_only_its_matching_private_nonce() {
    let mut b = good();
    let expected = b.stable_digest();
    let (a, _, _) = observed(&mut b);
    let a = a.unwrap();
    assert_eq!(a.bundle_digest, expected);
    assert!(b.source_generation_live.matches(&a.nonce));
    assert!(a.authorizes_bundle(&b));
}
#[test]
fn invalid_bundle_returns_all_original_inner_errors_without_consuming_the_one_shot_slot() {
    let mut b = bad();
    let expected = b.validate().unwrap_err();
    let (result, _, _) = observed(&mut b);
    assert!(matches!(result,Err(MintError::InvalidBundle(rows))if rows==expected));
    assert!(b.source_generation_live.0.is_none());
}
#[test]
fn already_minted_precedes_validation_and_never_changes_original_nonce() {
    let mut b = good();
    let a = SourceGenerationAuthority::mint_from_live_lowering(&mut b).unwrap();
    let ptr = Arc::as_ptr(&a.nonce);
    b.schema_version = 0;
    let (result, _, end) = observed(&mut b);
    assert_eq!(classify(&result), Err(MintError::AlreadyMinted));
    assert!(end < 20);
    assert!(b.source_generation_live.matches(&a.nonce));
    assert_eq!(ptr, Arc::as_ptr(&a.nonce));
}
#[test]
fn equal_cloned_content_gets_its_own_distinct_one_shot_source_identity() {
    let mut b = good();
    let a = SourceGenerationAuthority::mint_from_live_lowering(&mut b).unwrap();
    let mut c = b.clone();
    let (other, _, _) = observed(&mut c);
    let other = other.unwrap();
    assert_eq!(b, c);
    assert!(a.authorizes_bundle(&b));
    assert!(other.authorizes_bundle(&c));
    assert!(!a.authorizes_bundle(&c));
    assert!(!other.authorizes_bundle(&b));
}
#[test]
fn full_unencodable_module_errors_are_returned_instead_of_hashing_or_issuing() {
    let mut b = bad();
    b.module.types.push(Ty::Error);
    let (result, _, _) = observed(&mut b);
    assert!(
        matches!(result,Err(MintError::InvalidBundle(rows))if rows.iter().any(|e|matches!(e,NativeVerificationBundleError::TrustIrModuleHasNoWireIdentity{..})))
    );
    assert!(b.source_generation_live.0.is_none());
}
#[test]
fn actual_full_kernel_less_validation_rejects_strong_opaque_vc_evidence_before_issuance() {
    let mut b = crate::request::tests::native_bundle();
    let (result, _, _) = observed(&mut b);
    assert!(
        matches!(result,Err(MintError::InvalidBundle(rows))if rows.iter().any(|e|matches!(e,NativeVerificationBundleError::TrustVcCertificateNotDischarged{..})))
    );
    assert!(b.source_generation_live.0.is_none());
}
#[test]
fn issued_capability_is_invalidated_by_later_content_mutation_as_in_original_query() {
    let mut b = good();
    let (a, _, _) = observed(&mut b);
    let a = a.unwrap();
    assert!(a.authorizes_bundle(&b));
    b.provenance.producer_version.push_str("-changed");
    assert!(!a.authorizes_bundle(&b));
}
#[test]
fn actual_embedded_module_tamper_after_issuance_requires_full_validation_even_same_digest() {
    let mut b = good();
    let (a, _, _) = observed(&mut b);
    let a = a.unwrap();
    b.module.name.push_str("-tampered");
    assert_eq!(a.bundle_digest, b.stable_digest());
    assert!(!a.authorizes_bundle(&b));
}
#[test]
fn zero_instruction_fuel_does_not_bypass_issuer_checks_or_replenish_original_owner() {
    let mut b = good();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let a = SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
        &mut b,
        &mut s,
        site(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(a.authorizes_bundle(&b));
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn full_raw_unicode_and_nul_provenance_tail_is_bound_in_the_actual_issued_digest() {
    let mut b = good();
    b.provenance.source_artifact = Some("whole λ\0尾".repeat(400));
    let expected = b.stable_digest();
    let (a, _, _) = observed(&mut b);
    assert_eq!(a.unwrap().bundle_digest, expected);
}
#[test]
fn observed_authority_retirement_never_resets_the_live_bundle_one_shot_marker() {
    let mut b = good();
    let (a, _, _) = observed(&mut b);
    let a = a.unwrap();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    a.retire_observed(&mut s, site()).unwrap();
    assert!(b.source_generation_live.0.is_some());
    assert_eq!(oracle(&b), Err(MintError::AlreadyMinted));
    let last = o.events.last().unwrap();
    assert_eq!(
        (last.phase, last.work, last.copy_bytes),
        (ExecutionPhase::Publication, 0, 0)
    );
}
#[test]
fn whole_inner_issuance_errors_have_consuming_original_session_retirement() {
    for mut b in [bad(), good()] {
        let (result, _, _) = observed(&mut b);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        dispose(result, &mut s);
        let last = o.events.last().unwrap();
        assert_eq!(
            (last.phase, last.work, last.copy_bytes),
            (ExecutionPhase::Publication, 0, 0)
        );
    }
}

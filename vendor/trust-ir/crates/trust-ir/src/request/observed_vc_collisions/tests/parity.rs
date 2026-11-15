// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn empty_requests_and_empty_vc_obligations_have_no_collision_rows() {
    observed(&bundle(vec![]));
    for mode in [
        Mode::ImportProofCertificates,
        Mode::MergeProofCertificates,
        Mode::DischargeProofObligations,
    ] {
        assert!(observed(&bundle(vec![vc(0, mode, &[])])).0.is_empty());
    }
}
#[test]
fn all_nine_vc_mode_pairs_preserve_import_merge_vs_discharge_classification() {
    for a in [
        Mode::ImportProofCertificates,
        Mode::MergeProofCertificates,
        Mode::DischargeProofObligations,
    ] {
        for b in [
            Mode::ImportProofCertificates,
            Mode::MergeProofCertificates,
            Mode::DischargeProofObligations,
        ] {
            let i = bundle(vec![vc(1, a, &[7]), vc(2, b, &[7])]);
            assert_eq!(
                observed(&i).0.len(),
                usize::from(
                    (a == Mode::DischargeProofObligations)
                        != (b == Mode::DischargeProofObligations)
                )
            );
        }
    }
}
#[test]
fn first_physical_importing_and_discharging_rows_win_not_smallest_id_or_last() {
    let rows = observed(&fixture()).0;
    assert_eq!(rows.len(), 3);
    assert!(rows.iter().all(|e|matches!(e,E::TrustVcObligationBothImportedAndDischarged{importing,discharging,..}if *importing==NativeRequestId::new(100)&&*discharging==NativeRequestId::new(40))));
}
#[test]
fn collision_output_is_unique_unsigned_ascending_through_max_id() {
    let i = bundle(vec![
        vc(1, Mode::ImportProofCertificates, &[u32::MAX, 9, 0, 1, 9]),
        vc(2, Mode::DischargeProofObligations, &[9, u32::MAX, 1, 0, 0]),
    ]);
    let rows = observed(&i).0;
    let ids: Vec<_> = rows
        .iter()
        .map(|e| match e {
            E::TrustVcObligationBothImportedAndDischarged { obligation, .. } => obligation.index(),
            _ => panic!("collision only"),
        })
        .collect();
    assert_eq!(ids, vec![0, 1, 9, u32::MAX]);
}
#[test]
fn duplicates_within_one_family_or_one_request_are_not_cross_mode_collisions() {
    for mode in [
        Mode::ImportProofCertificates,
        Mode::MergeProofCertificates,
        Mode::DischargeProofObligations,
    ] {
        let i = bundle(vec![vc(1, mode, &[1, 1, 2]), vc(2, mode, &[2, 1])]);
        assert!(observed(&i).0.is_empty());
    }
}
#[test]
fn equal_request_ids_do_not_silence_cross_mode_ambiguity() {
    let i = bundle(vec![
        vc(8, Mode::ImportProofCertificates, &[1]),
        vc(8, Mode::DischargeProofObligations, &[1]),
    ]);
    assert!(
        matches!(observed(&i).0.as_slice(),[E::TrustVcObligationBothImportedAndDischarged{importing,discharging,..}]if importing==discharging)
    );
}
#[test]
fn mc_and_wp_requests_with_same_obligations_are_ignored_exactly() {
    let mut original = crate::request::tests::native_bundle();
    original.requests.remove(0);
    assert!(observed(&original).0.is_empty());
    let mut i = fixture();
    i.requests.extend(original.requests);
    assert_eq!(observed(&i).0, ordinary(&fixture()));
}
#[test]
fn unrelated_formula_name_options_and_provenance_do_not_enter_this_leaf() {
    let i = fixture();
    let (rows, a, end) = observed(&i);
    let mut changed = i.clone();
    for r in &mut changed.requests {
        if let NativeVerificationRequest::TrustVc(r) = r {
            r.provenance.expected_verifier.name = "x".repeat(8000);
            r.certificates.clear();
            r.lineage_roots.clear();
            r.function = None;
        }
    }
    let (new, b, end_b) = observed(&changed);
    assert_eq!(rows, new);
    assert_eq!(&a.events[..end], &b.events[..end_b]);
}
#[test]
fn earlier_empty_family_row_does_not_claim_later_obligation_first_id() {
    let i = bundle(vec![
        vc(1, Mode::ImportProofCertificates, &[]),
        vc(2, Mode::DischargeProofObligations, &[]),
        vc(3, Mode::MergeProofCertificates, &[1]),
        vc(4, Mode::DischargeProofObligations, &[1]),
    ]);
    assert!(
        matches!(observed(&i).0.as_slice(),[E::TrustVcObligationBothImportedAndDischarged{importing,discharging,..}]if *importing==NativeRequestId::new(3)&&*discharging==NativeRequestId::new(4))
    );
}
#[test]
fn no_collision_is_not_a_certificate_or_request_admission() {
    let i = bundle(vec![vc(0, Mode::ImportProofCertificates, &[1])]);
    assert!(observed(&i).0.is_empty());
    assert!(i.validate().is_err());
}

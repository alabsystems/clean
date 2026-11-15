// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn all_three_vc_modes_match_actual_full_original_projection() {
    for mode in [
        Mode::ImportProofCertificates,
        Mode::MergeProofCertificates,
        Mode::DischargeProofObligations,
    ] {
        let mut b = bad();
        vc(&mut b).mode = mode;
        observed(&b, 0);
    }
}
#[test]
fn mc_and_wp_skip_only_this_leaf_with_whole_observed_empty_result() {
    let b = fixture();
    assert!(observed(&b, 1).0.is_empty());
    assert!(observed(&b, 2).0.is_empty());
}
#[test]
fn invalid_actual_request_index_is_typed_error_not_empty_success() {
    let b = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for index in [b.requests.len(), usize::MAX] {
        assert_eq!(
            b.request_vc_shape_errors_observed(index, &mut s, site()),
            Err(ObservedValueError::InvalidRange)
        );
    }
    assert!(s.first_refusal().is_none());
}
#[test]
fn discharge_sites_use_sorted_unique_ids_then_every_physical_carried_certificate() {
    let b = bad();
    let rows = observed(&b, 0).0;
    assert!(
        matches!(rows.as_slice(),[E::TrustVcDischargeObligationNotSitedInFunction{obligation:a,actual:None,..},E::TrustVcDischargeObligationNotSitedInFunction{obligation:c,actual:Some(_),..},E::TrustVcDischargeRequestCarriesCertificate{..},E::TrustVcDischargeRequestCarriesCertificate{..}]if a.index()==0&&c.index()==1)
    );
}
#[test]
fn absent_discharge_function_skips_site_walk_then_precedes_carried_errors() {
    let mut b = bad();
    vc(&mut b).function = None;
    let rows = observed(&b, 0).0;
    assert!(matches!(
        rows.as_slice(),
        [
            E::MissingTrustVcDischargeFunction(_),
            E::TrustVcDischargeRequestCarriesCertificate { .. },
            E::TrustVcDischargeRequestCarriesCertificate { .. }
        ]
    ));
}
#[test]
fn imports_and_merges_report_missing_evidence_for_each_physical_obligation() {
    for mode in [Mode::ImportProofCertificates, Mode::MergeProofCertificates] {
        let mut b = importing();
        vc(&mut b).mode = mode;
        let rows = observed(&b, 0).0;
        let ids: Vec<_> = rows
            .iter()
            .map(|e| match e {
                E::MissingTrustVcEvidenceForObligation { obligation, .. } => obligation.index(),
                _ => panic!("missing only"),
            })
            .collect();
        assert_eq!(ids, vec![1, 0, 1, 88]);
    }
}
#[test]
fn certificate_obligation_presence_does_not_inspect_prover_digest_or_status() {
    let mut b = importing();
    let r = vc(&mut b);
    r.obligations = vec![ProofId::new(99)];
    r.certificates = vec![ProofCertificateRef {
        obligation: ProofId::new(99),
        prover: String::new(),
        evidence_digest: ProofDigest::sha256([0; 32]),
    }];
    assert!(observed(&b, 0).0.is_empty());
    assert!(b.validate().is_err());
}
#[test]
fn first_actual_ir_obligation_site_wins_over_later_exact_duplicate() {
    let mut b = bad();
    let mut exact = b.module.proof_obligations[0].clone();
    exact.site = Some(ObligationSite::new(FuncId::new(0), BlockId::new(0), 0));
    b.module.proof_obligations.push(exact);
    assert!(observed(&b,0).0.iter().any(|e|matches!(e,E::TrustVcDischargeObligationNotSitedInFunction{obligation,actual:None,..}if obligation.index()==0)));
    let last = b.module.proof_obligations.len() - 1;
    b.module.proof_obligations.swap(0, last);
    assert!(!observed(&b,0).0.iter().any(|e|matches!(e,E::TrustVcDischargeObligationNotSitedInFunction{obligation,..}if obligation.index()==0)));
}
#[test]
fn compiler_sidecar_function_claim_does_not_replace_actual_ir_site() {
    let mut b = bad();
    for s in &mut b.compiler_facts.obligation_sources {
        s.function = Some(FuncId::new(0));
    }
    let rows = observed(&b, 0).0;
    assert!(rows.iter().any(|e| matches!(
        e,
        E::TrustVcDischargeObligationNotSitedInFunction { actual: None, .. }
    )));
    b.module.proof_obligations[0].site =
        Some(ObligationSite::new(FuncId::new(0), BlockId::new(0), 0));
    for s in &mut b.compiler_facts.obligation_sources {
        s.function = Some(FuncId::new(9));
    }
    assert!(!observed(&b,0).0.iter().any(|e|matches!(e,E::TrustVcDischargeObligationNotSitedInFunction{obligation,..}if obligation.index()==0)));
}
#[test]
fn unknown_declared_obligation_skips_only_site_error() {
    let mut b = bad();
    vc(&mut b).obligations = vec![ProofId::new(u32::MAX)];
    assert!(
        observed(&b, 0)
            .0
            .iter()
            .all(|e| matches!(e, E::TrustVcDischargeRequestCarriesCertificate { .. }))
    );
}
#[test]
fn every_duplicate_carried_certificate_is_reported_even_when_equal() {
    let mut b = bad();
    let c = vc(&mut b).certificates[0].clone();
    vc(&mut b).certificates = vec![c; 4];
    assert_eq!(
        observed(&b, 0)
            .0
            .iter()
            .filter(|e| matches!(e, E::TrustVcDischargeRequestCarriesCertificate { .. }))
            .count(),
        4
    );
}
#[test]
fn whole_raw_long_unicode_carried_provers_outlive_original_bundle() {
    let mut b = bad();
    vc(&mut b).certificates[0].prover = "raw λ\0尾".repeat(1000);
    let expected = ordinary(&b, 0);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_vc_shape_errors_observed(0, &mut s, site())
        .unwrap();
    drop(b);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn original_request_ids_and_full_u32_site_function_ids_are_not_truncated() {
    let mut b = bad();
    let r = vc(&mut b);
    r.id = NativeRequestId::new(u32::MAX);
    r.function = Some(FuncId::new(u32::MAX));
    let rows = observed(&b, 0).0;
    assert!(rows.iter().all(|e| match e {
        E::TrustVcDischargeObligationNotSitedInFunction {
            request, expected, ..
        } => request.index() == u32::MAX && expected.index() == u32::MAX,
        E::TrustVcDischargeRequestCarriesCertificate { request, .. } => request.index() == u32::MAX,
        _ => false,
    }));
}
#[test]
fn successful_shape_does_not_replace_unconditional_certificate_replay_checks() {
    let b = fixture();
    assert!(observed(&b, 0).0.is_empty());
    assert!(
        b.request_errors_original_for_observed_tests()
            .iter()
            .any(|e| matches!(e, E::TrustVcCertificateNotDischarged { .. }))
    );
}

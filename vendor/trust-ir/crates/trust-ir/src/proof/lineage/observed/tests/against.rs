// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn tables(manifest: &ProofLineageManifest) -> (Vec<ProofObligation>, Vec<ProofCertificate>) {
    let obligations = manifest
        .nodes
        .iter()
        .map(|n| {
            ProofObligation::new(
                n.obligations[0],
                ObligationKind::TranslationValidation,
                crate::ProofStatus::Pending,
                "identity only",
            )
        })
        .collect();
    let certificates = manifest
        .nodes
        .iter()
        .map(|n| ProofCertificate {
            obligation: n.obligations[0],
            prover: "prover".into(),
            evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),
            assurance: None,
        })
        .collect();
    (obligations, certificates)
}
fn bound() -> (
    ProofLineageManifest,
    Vec<ProofObligation>,
    Vec<ProofCertificate>,
) {
    let mut manifest = fixture();
    let (obligations, certificates) = tables(&manifest);
    for (node, certificate) in manifest.nodes.iter_mut().zip(&certificates) {
        node.certificates = vec![certificate.lineage_ref()];
    }
    (manifest, obligations, certificates)
}
fn parity(
    manifest: &ProofLineageManifest,
    obligations: &[ProofObligation],
    certificates: &[ProofCertificate],
) -> Vec<ProofLineageError> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = manifest
        .against_errors_observed(obligations, certificates, &mut session, site())
        .unwrap();
    assert_eq!(
        errors,
        manifest
            .validate_against(obligations, certificates)
            .err()
            .unwrap_or_default()
    );
    errors
}
#[test]
fn complete_against_check_preserves_matching_unknown_missing_and_wrong_digest_diagnostics() {
    let (manifest, obligations, certificates) = bound();
    assert!(parity(&manifest, &obligations, &certificates).is_empty());
    assert!(
        manifest
            .lineage_is_closed(&obligations, &certificates)
            .is_err()
    );
    parity(&manifest, &[], &[]);
    let mut changed = certificates.clone();
    changed[0].evidence = ProofEvidence::SmtProof(vec![9]);
    assert!(
        parity(&manifest, &obligations, &changed)
            .iter()
            .any(|e| matches!(e, ProofLineageError::CertificateDigestMismatch { .. }))
    );
    changed[0].prover = "other".into();
    assert!(
        parity(&manifest, &obligations, &changed)
            .iter()
            .any(|e| matches!(e, ProofLineageError::MissingCertificate { .. }))
    );
}
#[test]
fn shape_errors_still_precede_module_matching_errors_without_discarding_either() {
    let (mut manifest, mut obligations, certificates) = bound();
    manifest.roots.push(ProofLineageId::new(999));
    obligations.clear();
    let errors = parity(&manifest, &obligations, &certificates);
    assert!(matches!(errors[0], ProofLineageError::MissingRoot(_)));
    assert!(matches!(
        errors[1],
        ProofLineageError::UnknownObligation { .. }
    ));
}
#[test]
fn actual_certificate_evidence_and_matching_interiors_use_original_stop_and_allowance() {
    let (manifest, obligations, certificates) = bound();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    manifest
        .against_errors_observed(&obligations, &certificates, &mut session, site())
        .unwrap();
    let first_digest = measured
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::CanonicalDigest)
        .unwrap()
        + 1;
    for stop in [first_digest, measured.events.len()] {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            manifest.against_errors_observed(&obligations, &certificates, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
    }
    let mut observer = Observer {
        work_limit: Some(measured.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    manifest
        .against_errors_observed(&obligations, &certificates, &mut session, site())
        .unwrap();
    assert_eq!(
        manifest.against_errors_observed(&obligations, &certificates, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}

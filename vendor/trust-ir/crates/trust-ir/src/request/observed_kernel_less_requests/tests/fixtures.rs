// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn fixture() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    for o in &mut b.module.proof_obligations {
        o.status = ProofStatus::Pending;
    }
    b
}
pub(super) fn vc(b: &mut NativeVerificationBundle) -> &mut TrustVcNativeRequest {
    match &mut b.requests[0] {
        NativeVerificationRequest::TrustVc(r) => r,
        _ => panic!("VC fixture"),
    }
}
pub(super) fn vc_ref(b: &NativeVerificationBundle) -> &TrustVcNativeRequest {
    match &b.requests[0] {
        NativeVerificationRequest::TrustVc(r) => r,
        _ => panic!("VC fixture"),
    }
}
pub(super) fn set_certificate(b: &mut NativeVerificationBundle, proof: ProofEvidence) {
    b.module.proof_certificates[0].evidence = proof;
    let reference = b.module.proof_certificates[0].lineage_ref();
    for n in &mut b.lineage.nodes {
        n.certificates = vec![reference.clone()];
    }
    vc(b).certificates = vec![reference];
}
pub(super) fn trusted() -> NativeVerificationBundle {
    let mut b = fixture();
    set_certificate(&mut b, ProofEvidence::Trusted("raw audit λ\0尾".into()));
    vc(&mut b).options.trusted_evidence = TrustVcTrustedEvidencePolicy::Reject;
    b
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = trusted();
    let r = vc(&mut b);
    r.mode = Mode::DischargeProofObligations;
    r.function = None;
    r.provenance.solvers.clear();
    r.certificates.push(r.certificates[0].clone());
    r.obligations = vec![ProofId::new(0), ProofId::new(0), ProofId::new(99)];
    let mut imported = vc_ref(&b).clone();
    imported.mode = Mode::MergeProofCertificates;
    imported.id = NativeRequestId::new(88);
    b.requests
        .push(NativeVerificationRequest::TrustVc(imported));
    b
}
pub(super) fn known(b: &NativeVerificationBundle) -> State {
    State {
        known: b
            .module
            .proof_certificates
            .iter()
            .map(|c| Known {
                reference: c.lineage_ref(),
                trusted: c.uses_trusted_evidence(),
            })
            .collect(),
        ..State::default()
    }
}
pub(super) fn authority_rows(rows: &[E]) -> Vec<&E> {
    rows.iter()
        .filter(|e| {
            matches!(
                e,
                E::TrustVcCertificateNotDischarged { .. } | E::TrustedCertificateRejected { .. }
            )
        })
        .collect()
}

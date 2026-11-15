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
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = fixture();
    b.module.proof_obligations[0].site = None;
    b.module.proof_obligations[1].site =
        Some(ObligationSite::new(FuncId::new(9), BlockId::new(0), 0));
    let r = vc(&mut b);
    r.mode = Mode::DischargeProofObligations;
    r.function = Some(FuncId::new(0));
    r.obligations = vec![
        ProofId::new(1),
        ProofId::new(0),
        ProofId::new(1),
        ProofId::new(88),
    ];
    r.certificates.push(ProofCertificateRef {
        obligation: ProofId::new(99),
        prover: "whole λ\0尾".into(),
        evidence_digest: ProofDigest::sha256([7; 32]),
    });
    b
}
pub(super) fn importing() -> NativeVerificationBundle {
    let mut b = fixture();
    let r = vc(&mut b);
    r.mode = Mode::ImportProofCertificates;
    r.obligations = vec![
        ProofId::new(1),
        ProofId::new(0),
        ProofId::new(1),
        ProofId::new(88),
    ];
    r.certificates.clear();
    b
}

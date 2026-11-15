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
    let mut wrong = b.module.proof_certificates[0].lineage_ref();
    wrong.evidence_digest = ProofDigest::sha256([9; 32]);
    let mut duplicate = wrong.clone();
    duplicate.evidence_digest = ProofDigest::sha256([10; 32]);
    let missing = ProofCertificateRef {
        obligation: ProofId::new(99),
        prover: "wrong λ\0尾".into(),
        evidence_digest: ProofDigest::sha256([11; 32]),
    };
    let r = vc(&mut b);
    r.obligations = vec![ProofId::new(1)];
    r.certificates = vec![wrong, duplicate, missing];
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest::sha256([55; 32]),
    };
    b
}

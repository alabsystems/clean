// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn ids(source: &[u32]) -> Vec<ProofId> {
    source.iter().copied().map(ProofId::new).collect()
}
pub(super) fn request(source: &[u32]) -> NativeVerificationRequest {
    let mut r = crate::request::tests::native_bundle().requests.remove(1);
    set_requested(&mut r, source);
    r
}
pub(super) fn set_requested(r: &mut NativeVerificationRequest, source: &[u32]) {
    match r {
        NativeVerificationRequest::TrustVc(r) => r.obligations = ids(source),
        NativeVerificationRequest::TrustMc(r) => r.obligations = ids(source),
        NativeVerificationRequest::TrustWp(r) => r.obligations = ids(source),
    }
}
pub(super) fn evidence(source: &[u32]) -> NativeEvidenceBundle {
    NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
        request: NativeRequestId::new(911),
        mode: TrustMcVerificationMode::Chc,
        obligations: ids(source),
        verifier: NativeToolIdentity::new("data only"),
        solvers: vec![],
        replay: ProofReplayIdentity::new("raw", "raw"),
        trust_ir_module_digest: ProofDigest::sha256([1; 32]),
        request_digest: ProofDigest::sha256([2; 32]),
        artifacts: vec![],
    })
}
pub(super) fn fixture() -> (NativeVerificationRequest, NativeEvidenceBundle) {
    (
        request(&[9, 7, 7, 2, 1, 0, 9, 5]),
        evidence(&[8, 7, 3, 3, 0, 8]),
    )
}

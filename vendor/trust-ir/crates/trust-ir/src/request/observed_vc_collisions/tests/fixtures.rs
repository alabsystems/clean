// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn vc(id: u32, mode: Mode, obligations: &[u32]) -> NativeVerificationRequest {
    let mut r = match crate::request::tests::native_bundle().requests.remove(0) {
        NativeVerificationRequest::TrustVc(r) => r,
        _ => panic!("VC fixture"),
    };
    r.id = NativeRequestId::new(id);
    r.mode = mode;
    r.obligations = obligations.iter().copied().map(ProofId::new).collect();
    NativeVerificationRequest::TrustVc(r)
}
pub(super) fn bundle(requests: Vec<NativeVerificationRequest>) -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.requests = requests;
    b
}
pub(super) fn fixture() -> NativeVerificationBundle {
    bundle(vec![
        vc(100, Mode::MergeProofCertificates, &[9, 1, 9, 3]),
        vc(300, Mode::ImportProofCertificates, &[1, 9]),
        vc(40, Mode::DischargeProofObligations, &[3, 9, 1, 9]),
        vc(20, Mode::DischargeProofObligations, &[9, 1]),
    ])
}

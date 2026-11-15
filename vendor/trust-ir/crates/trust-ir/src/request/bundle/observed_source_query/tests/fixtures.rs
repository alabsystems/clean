// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn good() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.requests.retain(|r| r.id() != NativeRequestId::new(0));
    b.evidence_bundles
        .retain(|e| e.request() != NativeRequestId::new(0));
    let digest = b.module.stable_digest();
    b.trust_ir_module_digest = digest;
    for n in &mut b.lineage.nodes {
        if b.lineage.roots.contains(&n.id) {
            n.target_module = digest;
        }
    }
    for e in &mut b.evidence_bundles {
        match e {
            NativeEvidenceBundle::TrustVc(e) => e.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustMc(e) => e.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustWp(e) => e.trust_ir_module_digest = digest,
        }
    }
    b
}
pub(super) fn minted() -> (SourceGenerationAuthority, NativeVerificationBundle) {
    let mut b = good();
    let a = SourceGenerationAuthority::mint_from_live_lowering(&mut b).unwrap();
    (a, b)
}
pub(super) fn tampered() -> (SourceGenerationAuthority, NativeVerificationBundle) {
    let (a, mut b) = minted();
    // Bundle's canonical preimage binds the stored module digest, not an
    // inlined module. Mutating actual module only therefore reaches the real
    // final validation while private nonce AND stored whole bundle hash match.
    b.module.name.push_str("-tampered");
    b.module.functions[0].name = "whole 'λ\0尾".repeat(300);
    b.module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Borrow {
            ptr: ValueId::new(0),
        }));
    assert_eq!(a.bundle_digest, b.stable_digest());
    assert!(b.validate().is_err());
    (a, b)
}

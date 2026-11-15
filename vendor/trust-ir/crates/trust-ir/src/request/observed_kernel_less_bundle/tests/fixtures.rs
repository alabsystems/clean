// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn good() -> NativeVerificationBundle {
    // Exact same construction as original source_generation_authority_bundle:
    // remove only deliberately unreplayed VC request/evidence, then refresh
    // actual current module identity in roots/evidence. No capability minted.
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
pub(super) fn with_evidence() -> NativeVerificationBundle {
    let mut b = good();
    b.evidence_bundles = b
        .requests
        .iter()
        .map(|r| {
            b.evidence_bundle_for_request(
                r,
                vec![NativeEvidenceArtifact::new(
                    "packet",
                    NativeEvidenceArtifactKind::Other,
                    ProofDigest::sha256([7; 32]),
                )],
            )
            .unwrap()
        })
        .collect();
    b
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = with_evidence();
    b.schema_version = u32::MAX;
    b.provenance.producer_version.clear();
    b.serialization.canonical_order = false;
    b.lineage.schema_version = u32::MAX;
    if let NativeVerificationRequest::TrustMc(r) = &mut b.requests[0] {
        r.options.chc.emit_horn_clauses = false;
        r.mode = TrustMcVerificationMode::Pdr;
        r.options.chc.pdr.enabled = false;
        r.options.chc.pdr.max_frames = Some(0);
    }
    if let NativeEvidenceBundle::TrustMc(e) = &mut b.evidence_bundles[0] {
        e.request_digest = ProofDigest::sha256([8; 32]);
        e.verifier.name = "WRONG".into();
    }
    b
}

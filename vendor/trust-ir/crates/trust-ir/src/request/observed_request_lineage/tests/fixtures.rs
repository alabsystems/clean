// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn digest(byte: u8) -> ProofDigest {
    ProofDigest::sha256([byte; 32])
}
pub(super) fn certificate(id: u32, name: &str, byte: u8) -> ProofCertificateRef {
    ProofCertificateRef {
        obligation: ProofId::new(id),
        prover: name.into(),
        evidence_digest: digest(byte),
    }
}
pub(super) fn node(id: u32, source: u8) -> ProofLineageNode {
    let mut n = ProofLineageNode::new(
        ProofLineageId::new(id),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "raw transform",
            "fixture",
            "v1",
        ),
        digest(source),
        digest(200),
    );
    n.obligations = vec![ProofId::new(id)];
    n.certificates = vec![certificate(id, "raw-prover", source)];
    n
}
pub(super) fn fixture() -> Input {
    let mut manifest = ProofLineageManifest::new();
    let mut a = node(0, 1);
    a.depends_on = vec![
        ProofLineageId::new(1),
        ProofLineageId::new(99),
        ProofLineageId::new(1),
    ];
    let mut b = node(1, 2);
    b.depends_on = vec![ProofLineageId::new(0)];
    manifest.nodes = vec![a, b, node(2, 3)];
    manifest.roots = vec![ProofLineageId::new(123)];
    Input {
        manifest,
        roots: vec![ProofLineageId::new(0), ProofLineageId::new(2)],
        source: Some(digest(2)),
    }
}

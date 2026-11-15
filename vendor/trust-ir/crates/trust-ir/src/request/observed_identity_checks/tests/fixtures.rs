// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) struct Fixture {
    pub(super) tool: NativeToolIdentity,
    pub(super) replay: ProofReplayIdentity,
    pub(super) cert: ProofCertificateRef,
}
pub(super) fn fixture() -> Fixture {
    Fixture {
        tool: NativeToolIdentity::new(" \u{2003}")
            .with_version("\t")
            .with_revision("\n")
            .with_digest(ProofDigest {
                algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                bytes: [0; 32],
            }),
        replay: ProofReplayIdentity::new("WRONG.NATIVE", " \u{3000}").with_transcript_digest(
            ProofDigest {
                algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                bytes: [0; 32],
            },
        ),
        cert: ProofCertificateRef {
            obligation: ProofId::new(71),
            prover: "WRONG.Native".into(),
            evidence_digest: ProofDigest::sha256([7; 32]),
        },
    }
}
pub(super) fn named(name: &str) -> Fixture {
    Fixture {
        tool: NativeToolIdentity::new(name),
        replay: ProofReplayIdentity::new(name, "invoke")
            .with_transcript_digest(ProofDigest::sha256([1; 32])),
        cert: ProofCertificateRef {
            obligation: ProofId::new(71),
            prover: name.into(),
            evidence_digest: ProofDigest::sha256([7; 32]),
        },
    }
}
pub(super) fn suites() -> [Suite; 8] {
    [
        Suite::Unknown,
        Suite::TrustVc,
        Suite::TrustMc,
        Suite::TrustWp,
        Suite::AY,
        Suite::TRust,
        Suite::TrustIr,
        Suite::Other,
    ]
}

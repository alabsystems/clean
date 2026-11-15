// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.child(b, Group::Identity, w)?;
        self.child(b, Group::References, w)?;
        // Preserve the two separate actual original fixed adapter getters.
        w.admit(
            1,
            size_of::<NativeAdapterInput>() + size_of::<Option<ProofDigest>>(),
        )?;
        if let Some(source) = b.source_digest() {
            w.admit(
                size_of::<ProofDigest>(),
                size_of::<ProofDigest>() + size_of::<bool>(),
            )?;
            if source.is_zero() {
                self.fixed(
                    || E::EmptyDigest {
                        field: "input.rust_mir.body_digest",
                    },
                    w,
                )?;
            }
        }
        w.admit(
            1,
            size_of::<NativeAdapterInput>() + size_of::<Option<ProofDigest>>(),
        )?;
        if let Some(source) = b.source_digest() {
            w.admit(1, size_of::<ProofDigestAlgorithm>() + size_of::<bool>())?;
            if source.algorithm != ProofDigestAlgorithm::Sha256 {
                self.fixed(
                    || E::NonCryptographicDigest {
                        field: "input.source_digest",
                    },
                    w,
                )?;
            }
        }
        w.admit(1, size_of::<usize>() + size_of::<bool>())?;
        if b.requests.is_empty() {
            self.fixed(|| E::EmptyRequests, w)?;
        }
        self.child(b, Group::Provenance, w)?;
        self.child(b, Group::Serialization, w)?;
        self.child(b, Group::Diagnostics, w)?;
        self.lineage(b, w)?;
        self.child(b, Group::Formula, w)?;
        self.child(b, Group::LineageDigests, w)?;
        self.child(b, Group::CompilerFacts, w)
    }
}

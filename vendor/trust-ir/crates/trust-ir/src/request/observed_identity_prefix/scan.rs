// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, 2 * size_of::<u32>() + size_of::<bool>())?;
        if b.schema_version != NativeVerificationBundle::SCHEMA_VERSION {
            self.fixed(|| E::UnsupportedSchemaVersion(b.schema_version), w)?;
        }
        w.admit(
            size_of::<ProofDigest>(),
            size_of::<ProofDigest>() + size_of::<bool>(),
        )?;
        if b.trust_ir_module_digest.is_zero() {
            self.fixed(
                || E::EmptyDigest {
                    field: "trust_ir_module_digest",
                },
                w,
            )?;
        }
        w.admit(1, size_of::<ProofDigestAlgorithm>() + size_of::<bool>())?;
        if b.trust_ir_module_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            self.fixed(
                || E::NonCryptographicDigest {
                    field: "trust_ir_module_digest",
                },
                w,
            )?;
        }
        // Capture COMPLETE owned child output before any next fee. Its empty
        // result, not a caller flag/callback, controls the original hash guard.
        w.admit(1, size_of::<Vec<E>>())?;
        self.batch = b.wire_identity_errors_observed(w.session, w.site)?;
        w.admit(1, size_of::<bool>())?;
        let encodable = self.batch.is_empty();
        self.flush(w)?;
        if encodable {
            w.admit(
                1,
                size_of::<Option<ProofDigest>>() + size_of::<ProofDigest>(),
            )?;
            self.actual = Some(b.module.checked_stable_digest_observed(w.session, w.site)?);
            w.admit(
                size_of::<ProofDigest>(),
                2 * size_of::<ProofDigest>() + size_of::<bool>(),
            )?;
            let actual = self.actual.ok_or(ObservedValueError::InvalidRange)?;
            if b.trust_ir_module_digest != actual {
                self.fixed(
                    || E::TrustIrModuleDigestMismatch {
                        expected: actual,
                        actual: b.trust_ir_module_digest,
                    },
                    w,
                )?;
            }
        }
        Ok(())
    }
}

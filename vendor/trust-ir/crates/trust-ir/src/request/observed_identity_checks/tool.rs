// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn tool<O: ExecutionObserver>(
        &mut self,
        field: &'static str,
        t: &NativeToolIdentity,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if w.blank(&t.name)? {
            self.fixed(|| E::EmptyProvenanceField(field), w)?;
        }
        w.admit(1, size_of::<Option<&String>>())?;
        if let Some(v) = &t.version
            && w.blank(v)?
        {
            self.fixed(
                || E::InvalidToolIdentityField {
                    field,
                    component: "version",
                },
                w,
            )?;
        }
        w.admit(1, size_of::<Option<&String>>())?;
        if let Some(v) = &t.revision
            && w.blank(v)?
        {
            self.fixed(
                || E::InvalidToolIdentityField {
                    field,
                    component: "revision",
                },
                w,
            )?;
        }
        w.admit(40, size_of::<Option<crate::ProofDigest>>())?;
        if let Some(d) = t.digest
            && d.is_zero()
        {
            self.fixed(|| E::EmptyDigest { field }, w)?;
        }
        w.admit(1, size_of::<Option<crate::ProofDigest>>())?;
        if t.digest
            .is_some_and(|d| d.algorithm != ProofDigestAlgorithm::Sha256)
        {
            self.fixed(
                || E::InvalidToolIdentityField {
                    field,
                    component: "digest.algorithm",
                },
                w,
            )?;
        }
        Ok(())
    }
    pub(super) fn verifier<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        suite: Suite,
        t: &NativeToolIdentity,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.normal(&t.name, w)?;
        w.admit(2, size_of::<Option<&str>>() + size_of::<bool>())?;
        if !self.canonical.is_empty()
            && let Some(family) = suite.canonical_family()
            && !self.family(family, w)?
        {
            self.named(&t.name, Kind::Verifier(request, suite), w)?;
        }
        Ok(())
    }
    pub(super) fn certificate<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        suite: Suite,
        c: &ProofCertificateRef,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Option<&str>>())?;
        let Some(family) = suite.canonical_family() else {
            return Ok(());
        };
        self.normal(&c.prover, w)?;
        // Unlike expected verifier/replay checks, the original certificate
        // helper refuses an empty canonical prover for a known family.
        if !self.family(family, w)? {
            self.named(
                &c.prover,
                Kind::Certificate(request, suite, c.obligation),
                w,
            )?;
        }
        Ok(())
    }
}

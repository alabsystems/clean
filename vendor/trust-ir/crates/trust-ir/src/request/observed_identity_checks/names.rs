// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Kind {
    Verifier(NativeRequestId, Suite),
    Replay(NativeRequestId, Suite),
    Certificate(NativeRequestId, Suite, crate::ProofId),
}
impl State {
    pub(super) fn normal<O: ExecutionObserver>(
        &mut self,
        name: &str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if !self.canonical.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        w.admit(1, size_of::<R<String>>() + size_of::<String>())?;
        self.canonical = canonical_tool_name_observed(name, w.session, w.site)?;
        Ok(())
    }
    pub(super) fn family<O: ExecutionObserver>(
        &mut self,
        family: &'static str,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        // Only Suite::canonical_family fixed ASCII strings (<=8 bytes) enter.
        // Actual helper compares whole length first, fixed prefix bytes and
        // one ASCII dash. It never scans a variable suffix or normalizes text.
        w.admit(4 * family.len() + 8, size_of::<bool>())?;
        Ok(canonical_name_matches_family(&self.canonical, family))
    }
    pub(super) fn named<O: ExecutionObserver>(
        &mut self,
        name: &str,
        kind: Kind,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.text(name, &mut self.text)?;
        w.admit(
            1,
            size_of::<E>() + size_of::<Option<E>>() + 2 * size_of::<String>(),
        )?;
        let raw = take(&mut self.text);
        let canonical = take(&mut self.canonical);
        self.pending = Some(match kind {
            Kind::Verifier(request, suite) => E::ExpectedVerifierIdentityMismatch {
                request,
                suite,
                verifier: raw,
                canonical,
            },
            Kind::Replay(request, expected) => E::ReplayIdentityVerifierSuiteMismatch {
                request,
                expected,
                engine: raw,
                canonical,
            },
            Kind::Certificate(request, expected, obligation) => {
                E::CertificateVerifierSuiteMismatch {
                    request,
                    expected,
                    obligation,
                    prover: raw,
                    canonical,
                }
            }
        });
        self.emit(w)
    }
}

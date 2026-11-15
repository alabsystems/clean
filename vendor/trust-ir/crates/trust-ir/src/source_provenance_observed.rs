// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual source-loop/name/place binding check under the original session.
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofDigest, ProofDigestAlgorithm, SourcePlace, SourceProvenance};
use core::mem::{size_of, take};
mod preimage;
mod semantic;
mod storage;
#[cfg(test)]
mod tests;
use storage::Writer;
type R<T = ()> = Result<T, ObservedValueError>;
const DOMAIN: &str = "trust_ir.source_provenance.binding.v1";
impl SourceProvenance {
    /// Check the exact existing binding preimage: schema, both tagged digests,
    /// full ordered loop rows and full UTF-8 names/place tags. Original u32
    /// count-prefix saturation is preserved WITHOUT truncating any real rows
    /// or payload bytes. This validates only this binding, never compiler HIR,
    /// semantic body identity, injectivity, source authority or full validity.
    ///
    /// Actual preimage construction, requested buffer growth, chunked hash and
    /// consuming buffer retirement share the supplied original session/site.
    /// Operational refusal is typed, never false or a smaller preimage. No
    /// public refresh/reseal method is introduced; only validity is exposed.
    pub fn binding_digest_is_valid_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let expected = binding_digest(self, session, site)?;
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 34,
            copy_bytes: size_of::<bool>(),
        })?;
        let valid = self.binding_digest == expected;
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })?;
        Ok(valid)
    }
}
fn binding_digest<O: ExecutionObserver>(
    source: &SourceProvenance,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ProofDigest> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::CanonicalSerialization,
        site,
        work: 1,
        copy_bytes: size_of::<Writer<'_, '_, O>>(),
    })?;
    let mut writer = Writer {
        session,
        site,
        bytes: Vec::new(),
    };
    let result = writer.preimage(source).and_then(|()| {
        ProofDigest::sha256_domain_observed(DOMAIN, &writer.bytes, writer.session, site)
    });
    writer.retire();
    let result = result.and_then(|digest| {
        writer.publication()?;
        Ok(digest)
    });
    result.map_err(|error| writer.terminal(error))
}

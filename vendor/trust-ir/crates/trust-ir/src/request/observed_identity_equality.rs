// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Raw derived identity equality under the caller's same original observer.
//! No normalization, validity, authenticated identity or replay is inferred.
use super::NativeToolIdentity;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofDigest, ProofReplayIdentity};
use core::mem::size_of;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T> = Result<T, ObservedValueError>;
impl NativeToolIdentity {
    /// Exact raw derived Eq, including all optional fields. Malformed equal
    /// records still compare equal; validity and permission remain separate.
    pub fn structural_eq_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<Work<'_, '_, O>>() + 2 * size_of::<&Self>())?;
        let Self {
            name,
            version,
            revision,
            digest,
        } = self;
        let Self {
            name: other_name,
            version: other_version,
            revision: other_revision,
            digest: other_digest,
        } = other;
        let equal = w.text(name, other_name)?
            && w.optional(version, other_version)?
            && w.optional(revision, other_revision)?
            && w.digest(digest, other_digest)?;
        w.publish(equal)
    }
}
impl ProofReplayIdentity {
    /// Exact raw engine/invocation/optional digest equality; no transcript or
    /// kernel is replayed and no canonical alias comparison is substituted.
    pub fn structural_eq_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<Work<'_, '_, O>>() + 2 * size_of::<&Self>())?;
        let Self {
            engine,
            invocation,
            transcript_digest,
        } = self;
        let Self {
            engine: other_engine,
            invocation: other_invocation,
            transcript_digest: other_digest,
        } = other;
        let equal = w.text(engine, other_engine)?
            && w.text(invocation, other_invocation)?
            && w.digest(transcript_digest, other_digest)?;
        w.publish(equal)
    }
}

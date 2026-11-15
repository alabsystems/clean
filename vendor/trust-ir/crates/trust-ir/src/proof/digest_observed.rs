// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Bounded updates of the existing canonical SHA-256 preimage. Constructing
//! that preimage and validating its authority remain separate obligations.

use super::ProofDigest;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use sha2::{Digest, Sha256};

const CHUNK_BYTES: usize = 1024;

impl ProofDigest {
    /// Hash exactly [`Self::sha256_domain`]'s versioned framing and borrowed
    /// bytes while observing the SAME original session before every bounded
    /// SHA update. No canonical byte buffer is allocated or copied wholesale.
    ///
    /// This primitive neither validates the input nor establishes authority.
    /// In particular it does not make upstream canonical serializers, module
    /// wire preparation or bundle validation cooperatively cancellable.
    pub fn sha256_domain_observed<O: ExecutionObserver>(
        domain: &str,
        bytes: &[u8],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Self, ObservedValueError> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 1,
            copy_bytes: core::mem::size_of::<Sha256>(),
        })?;
        let domain_len = u64::try_from(domain.len())
            .map_err(|_| ObservedValueError::CapacityOverflow)?
            .to_be_bytes();
        let payload_len = u64::try_from(bytes.len())
            .map_err(|_| ObservedValueError::CapacityOverflow)?
            .to_be_bytes();
        let mut hasher = Sha256::new();
        for part in [
            b"trust-ir.sha256-domain.v1\0".as_slice(),
            &domain_len,
            domain.as_bytes(),
            &payload_len,
            bytes,
        ] {
            for chunk in part.chunks(CHUNK_BYTES) {
                session.admit(ExecutionProgress {
                    phase: ExecutionPhase::CanonicalDigest,
                    site,
                    work: chunk.len(),
                    copy_bytes: chunk.len(),
                })?;
                hasher.update(chunk);
            }
        }
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 128,
            copy_bytes: core::mem::size_of::<Self>(),
        })?;
        let digest = Self::sha256(hasher.finalize().into());
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })?;
        Ok(digest)
    }
}

#[cfg(test)]
mod tests;

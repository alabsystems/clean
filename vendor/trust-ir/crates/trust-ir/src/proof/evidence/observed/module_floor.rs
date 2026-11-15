// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact core module CleanCic identity floor, explicitly NOT replay verdict.
use super::*;
use crate::{Module, proof::ProofObligation};
#[cfg(test)]
mod tests;
impl ProofCertificate {
    /// Only the conjunction preceding the actual kernel call in ordinary
    /// CleanCicModuleProofAuthority::replays_authority. A true value means
    /// merely that actual kernel replay MAY now be attempted. It cannot
    /// discharge/certify a claim or substitute for the real kernel verdict.
    /// No callback, public status or candidate replay currency is accepted.
    #[allow(
        dead_code,
        reason = "staged by the observed-r23 lane with no production caller yet; its tests drive it"
    )]
    pub(crate) fn clean_cic_module_identity_floor_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        row: &ProofObligation,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 8,
            copy_bytes: 2 * size_of::<crate::ProofId>()
                + size_of::<&ProofEvidence>()
                + size_of::<usize>()
                + size_of::<bool>(),
        })?;
        let eligible = if self.obligation != row.id {
            false
        } else if let ProofEvidence::CleanCic { term, .. } = &self.evidence {
            if term.is_empty() {
                false
            } else {
                s.admit(ExecutionProgress {
                    phase: ExecutionPhase::CanonicalDigest,
                    site,
                    work: 1,
                    copy_bytes: size_of::<R<bool>>() + size_of::<bool>(),
                })?;
                self.evidence
                    .clean_cic_lineage_binds_in_module_observed(row, module, s, site)?
            }
        } else {
            false
        };
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(eligible)
    }
}

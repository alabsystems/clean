// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual core module_symbol_resolver semantics; lineage DATA, never replay.
//! Existing catalog-unique APIs and their event sequence remain untouched.
use super::*;
use crate::Module;
mod content;
mod lookup;
#[cfg(test)]
mod tests;
impl ProofObligation {
    /// Exact v8 lineage DATA with the actual module_symbol_resolver, including
    /// indexed-ID-first and then FIRST physical fallback. This differs from
    /// the existing builder catalog-unique API on malformed duplicate IDs.
    /// No resolver callback, kernel verdict, or authority is accepted/created.
    pub fn clean_cic_lineage_digest_v8_in_module_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        binding: Option<&CertificateBinding>,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<ProofDigest>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<R<Option<ProofDigest>>>())?;
        let mut st = State::default();
        let result = (|| -> R<Option<ProofDigest>> {
            if !st.module_content(self, module, &mut w)? {
                return Ok(None);
            }
            st.u8(u8::from(binding.is_some()), &mut w)?;
            if let Some(binding) = binding {
                st.binding(binding, &mut w)?;
            }
            w.admit(
                1,
                size_of::<R<ProofDigest>>() + size_of::<Option<ProofDigest>>(),
            )?;
            Ok(Some(ProofDigest::sha256_domain_observed(
                "trust_ir.proof.clean_cic.lineage.v8",
                &st.bytes,
                w.session,
                w.site,
            )?))
        })();
        st.finish_module_digest(result, &mut w)
    }
}
impl ProofEvidence {
    /// Exact ordinary clean_cic_lineage_binds with the real module resolver.
    /// Index lineage is tried first and short-circuits v8, just as the actual
    /// core NativeProofAuthority floor. Matching lineage is still only DATA.
    pub fn clean_cic_lineage_binds_in_module_observed<O: ExecutionObserver>(
        &self,
        row: &ProofObligation,
        module: &Module,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 64,
            copy_bytes: size_of::<R<ProofDigest>>() + size_of::<ProofDigest>() + size_of::<bool>(),
        })?;
        let matches = if let ProofEvidence::CleanCic { lineage, .. } = self {
            let indexed = row.clean_cic_lineage_digest_observed(s, site)?;
            s.admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalDigest,
                site,
                work: 34,
                copy_bytes: 2 * size_of::<ProofDigest>() + size_of::<bool>(),
            })?;
            if *lineage == indexed {
                true
            } else {
                self.clean_cic_lineage_is_v8_in_module_observed(row, module, s, site)?
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
        Ok(matches)
    }
    pub fn clean_cic_lineage_is_v8_in_module_observed<O: ExecutionObserver>(
        &self,
        row: &ProofObligation,
        module: &Module,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 64,
            copy_bytes: size_of::<R<Option<ProofDigest>>>() + size_of::<Option<ProofDigest>>(),
        })?;
        let matches = if let ProofEvidence::CleanCic {
            lineage,
            kernel_recheck,
            ..
        } = self
        {
            let binding = kernel_recheck.as_ref().and_then(|r| r.binding.as_deref());
            let digest =
                row.clean_cic_lineage_digest_v8_in_module_observed(module, binding, s, site)?;
            s.admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalDigest,
                site,
                work: 35,
                copy_bytes: size_of::<Option<ProofDigest>>()
                    + size_of::<ProofDigest>()
                    + size_of::<bool>(),
            })?;
            digest.is_some_and(|digest| digest == *lineage)
        } else {
            false
        };
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(matches)
    }
}

impl State {
    fn finish_module_digest<O: ExecutionObserver>(
        &mut self,
        result: R<Option<ProofDigest>>,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<ProofDigest>> {
        self.retire(w);
        result.and_then(|digest| {
            w.session.admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: w.site,
                work: 1,
                copy_bytes: size_of::<Option<ProofDigest>>() + size_of::<R<Option<ProofDigest>>>(),
            })?;
            Ok(digest)
        }) // Already-held local error survives later cleanup refusal.
    }
}

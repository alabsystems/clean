// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn evidence<O: ExecutionObserver>(
        &mut self,
        evidence: &ProofEvidence,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(64, size_of::<&ProofEvidence>())?;
        match evidence {
            ProofEvidence::SmtProof(data) => {
                self.u8(0, w)?;
                self.blob(data, w)
            }
            ProofEvidence::LeanProof(text) => {
                self.u8(1, w)?;
                self.blob(text.as_bytes(), w)
            }
            ProofEvidence::KaniHarness(text) => {
                self.u8(2, w)?;
                self.blob(text.as_bytes(), w)
            }
            ProofEvidence::GammaCrownBound {
                epsilon,
                verified_layers,
            } => {
                self.u8(3, w)?;
                w.admit(1, size_of::<[u8; 8]>())?;
                w.append(&epsilon.to_bits().to_le_bytes(), &mut self.bytes)?;
                self.u32(*verified_layers, w)
            }
            ProofEvidence::TranslationValidation {
                rule_name,
                smt_hash,
            } => {
                self.u8(4, w)?;
                self.blob(rule_name.as_bytes(), w)?;
                w.append(smt_hash, &mut self.bytes)
            }
            ProofEvidence::Trusted(reason) => {
                self.u8(5, w)?;
                self.blob(reason.as_bytes(), w)
            }
            ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external,
            } => {
                self.u8(if external.is_some() { 8 } else { 6 }, w)?;
                self.u32(callee.index(), w)?;
                self.u32(obligation.index(), w)?;
                if let Some(reference) = external {
                    self.u32(reference.module.index(), w)?;
                    self.blob(reference.symbol.as_bytes(), w)?;
                    self.u8(u8::from(reference.obligation.is_some()), w)?;
                    if let Some(id) = reference.obligation {
                        self.u32(id.index(), w)?;
                    }
                }
                Ok(())
            }
            ProofEvidence::CleanCic {
                term,
                context,
                lineage,
                kernel_recheck,
            } => {
                self.u8(7, w)?;
                self.blob(term, w)?;
                self.blob(context, w)?;
                self.digest_bytes(lineage, w)?;
                self.u8(u8::from(kernel_recheck.is_some()), w)?;
                if let Some(directive) = kernel_recheck {
                    self.directive(directive, w)?;
                }
                Ok(())
            }
        }
    }
    fn directive<O: ExecutionObserver>(
        &mut self,
        source: &CleanCicKernelRecheck,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.blob(source.module.as_bytes(), w)?;
        self.strings(&source.theorems, w)?;
        self.blob(source.anchor.as_bytes(), w)?;
        self.strings(&source.allowed_axioms, w)?;
        // Historical unbound identities have NO trailing absence byte.
        if let Some(binding) = &source.binding {
            self.u8(1, w)?;
            self.binding(binding, w)?;
        }
        Ok(())
    }
    pub(super) fn strings<O: ExecutionObserver>(
        &mut self,
        rows: &[String],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.length(rows.len(), w)?;
        let mut at = 0;
        while let Some(row) = w.at(rows, at)? {
            self.blob(row.as_bytes(), w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn u8<O: ExecutionObserver>(&mut self, value: u8, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, size_of::<[u8; 1]>())?;
        w.append(&[value], &mut self.bytes)
    }
    pub(super) fn u32<O: ExecutionObserver>(&mut self, value: u32, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, size_of::<[u8; 4]>())?;
        w.append(&value.to_le_bytes(), &mut self.bytes)
    }
    pub(super) fn length<O: ExecutionObserver>(
        &mut self,
        value: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<[u8; 8]>())?;
        let value = u64::try_from(value).map_err(|_| ObservedValueError::CapacityOverflow)?;
        w.append(&value.to_le_bytes(), &mut self.bytes)
    }
    pub(super) fn blob<O: ExecutionObserver>(
        &mut self,
        value: &[u8],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.length(value.len(), w)?;
        w.append(value, &mut self.bytes)
    }
    pub(super) fn digest_bytes<O: ExecutionObserver>(
        &mut self,
        value: &ProofDigest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.u8(
            match value.algorithm {
                ProofDigestAlgorithm::Sha256 => 0,
                ProofDigestAlgorithm::TrustIrStableV1 => 1,
            },
            w,
        )?;
        w.append(&value.bytes, &mut self.bytes)
    }
}

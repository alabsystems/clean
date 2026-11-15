// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<O: ExecutionObserver> Writer<'_, '_, O> {
    pub(super) fn preimage(&mut self, source: &SourceProvenance) -> R {
        self.admit(4, size_of::<u32>() + 2 * size_of::<ProofDigest>())?;
        self.u32(source.schema)?;
        self.digest(&source.compiler_source_digest)?;
        self.digest(&source.semantic_body_digest)?;
        self.count(source.loops.len())?;
        let mut index = 0usize;
        loop {
            self.admit(1, size_of::<&crate::SourceLoopProvenance>())?;
            let Some(row) = source.loops.get(index) else {
                return Ok(());
            };
            self.u32(row.source_loop_id)?;
            self.u32(row.hir_local_id)?;
            self.u32(row.header.index())?;
            self.count(row.bindings.len())?;
            let mut binding = 0usize;
            loop {
                self.admit(1, size_of::<&crate::SourceBindingProvenance>())?;
                let Some(row) = row.bindings.get(binding) else {
                    break;
                };
                self.count(row.name.len())?;
                self.append(row.name.as_bytes())?;
                self.u32(row.hir_local_id)?;
                self.admit(2, size_of::<crate::SourcePlace>())?;
                match row.place {
                    SourcePlace::FunctionParameter { index } => {
                        self.append(&[0])?;
                        self.u32(index)?;
                    }
                    SourcePlace::LoopParameter { index } => {
                        self.append(&[1])?;
                        self.u32(index)?;
                    }
                }
                binding = binding
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    pub(super) fn u32(&mut self, value: u32) -> R {
        self.admit(4, 4)?;
        self.append(&value.to_be_bytes())
    }
    pub(super) fn count(&mut self, count: usize) -> R {
        self.admit(1, size_of::<u32>())?;
        self.u32(u32::try_from(count).unwrap_or(u32::MAX))
    }
    fn digest(&mut self, digest: &ProofDigest) -> R {
        self.admit(2, size_of::<ProofDigest>())?;
        self.append(&[match digest.algorithm {
            ProofDigestAlgorithm::Sha256 => 0,
            ProofDigestAlgorithm::TrustIrStableV1 => 1,
        }])?;
        self.append(&digest.bytes)
    }
}

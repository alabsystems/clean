// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual sole-function, no-provenance module identity preimage.
use super::*;
use crate::{FuncId, Module};
#[cfg(test)]
mod tests;
const SEMANTIC_DOMAIN: &str = "trust_ir.source_provenance.semantic_function.v2";
#[derive(Default)]
struct State {
    error: String,
}
impl Module {
    /// Same semantic body identity and missing/duplicate error String as the
    /// ordinary method, inside a separate typed operational Result. All actual
    /// uniqueness scans, exact borrowed module projection, string collection,
    /// count/hash passes and final37-byte seal use the supplied original owner.
    ///
    /// The projection keeps all module tables/sidecars/name, emits the unique
    /// selected function alone and omits its source_provenance in BOTH walks.
    /// No whole-module clone, opaque serializer, renewed owner or fallback is
    /// used. Unsupported/stop/capacity/cleanup returns operational Err rather
    /// than an accepting smaller identity. Identity does not establish HIR,
    /// binding/source authority, module validity, ABI truth or proof validity.
    pub fn source_provenance_semantic_digest_observed<O: ExecutionObserver>(
        &self,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<ProofDigest, String>> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalSerialization,
            site,
            work: 1,
            copy_bytes: size_of::<State>() + size_of::<Writer<'_, '_, O>>(),
        })?;
        let mut state = State::default();
        let mut writer = Writer {
            session,
            site,
            bytes: Vec::new(),
        };
        let result = state.identity(self, function, &mut writer);
        writer.retire();
        match result.and_then(|digest| {
            writer.publication()?;
            Ok(digest)
        }) {
            Ok(Some(digest)) => Ok(Ok(digest)),
            Ok(None) => Ok(Err(take(&mut state.error))),
            Err(error) => {
                state.retire(&mut writer);
                Err(writer.terminal(error))
            }
        }
    }
}
impl State {
    fn identity<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: FuncId,
        writer: &mut Writer<'_, '_, O>,
    ) -> R<Option<ProofDigest>> {
        let mut selected = None;
        let mut duplicate = false;
        let mut index = 0usize;
        loop {
            writer.admit(2, size_of::<&crate::Function>())?;
            let Some(candidate) = module.functions.get(index) else {
                break;
            };
            if candidate.id == function {
                if selected.is_some() {
                    duplicate = true;
                } else {
                    selected = Some(index);
                }
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        let Some(index) = selected.filter(|_| !duplicate) else {
            self.target_error(function, writer)?;
            return Ok(None);
        };
        let module_digest = crate::binary::observed_source_function_identity(
            module,
            index,
            writer.session,
            writer.site,
        )?;
        writer.admit(37, 37)?;
        let mut bytes = [0u8; 37];
        bytes[..4].copy_from_slice(&function.index().to_be_bytes());
        bytes[4] = match module_digest.algorithm {
            ProofDigestAlgorithm::Sha256 => 0,
            ProofDigestAlgorithm::TrustIrStableV1 => 1,
        };
        bytes[5..].copy_from_slice(&module_digest.bytes);
        let digest = ProofDigest::sha256_domain_observed(
            SEMANTIC_DOMAIN,
            &bytes,
            writer.session,
            writer.site,
        )?;
        Ok(Some(digest))
    }
    fn target_error<O: ExecutionObserver>(
        &mut self,
        function: FuncId,
        writer: &mut Writer<'_, '_, O>,
    ) -> R {
        writer.admit(2, 0)?;
        if self.error.capacity() != 0 || writer.bytes.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        writer.append(b"source provenance target function #")?;
        writer.admit(10, 10)?;
        let mut digits = [0u8; 10];
        let mut begin = digits.len();
        let mut number = function.index();
        loop {
            writer.admit(1, 0)?;
            begin = begin
                .checked_sub(1)
                .ok_or(ObservedValueError::InvalidRange)?;
            digits[begin] =
                b'0' + u8::try_from(number % 10).map_err(|_| ObservedValueError::InvalidRange)?;
            number /= 10;
            if number == 0 {
                break;
            }
        }
        writer.append(&digits[begin..])?;
        writer.append(b" is missing or duplicated")?;
        // Exact bounded ASCII diagnostic. Recover the owned Vec immediately
        // on an unexpected UTF-8 error, before any fallible return/cleanup.
        writer.admit(writer.bytes.len(), size_of::<String>())?;
        self.error = match String::from_utf8(take(&mut writer.bytes)) {
            Ok(error) => error,
            Err(error) => {
                writer.bytes = error.into_bytes();
                return Err(ObservedValueError::InvalidRange);
            }
        };
        Ok(())
    }
    fn retire<O: ExecutionObserver>(&mut self, writer: &mut Writer<'_, '_, O>) {
        writer.session.retirement_step(writer.site, 1);
        drop(take(&mut self.error));
        writer.session.retirement_poll(writer.site);
    }
}

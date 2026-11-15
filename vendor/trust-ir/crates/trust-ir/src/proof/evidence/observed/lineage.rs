// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original v5/v6/v7/v8 lineage DATA; never kernel authority.
use super::*;
use crate::ModuleFunctionCatalog;
use crate::proof::ProofObligation;
mod fields;
mod module;
use fields::FormulaBindings;
mod sorts;
#[cfg(test)]
mod tests;
impl ProofObligation {
    pub fn clean_cic_lineage_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ProofDigest> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>())?;
        let mut state = State::default();
        let result = state.index_lineage(self, &mut w);
        state.retire(&mut w);
        result
            .and_then(|digest| w.publication().map(|()| digest))
            .map_err(|e| w.terminal(e))
    }
    /// Same original content, using only the actual unique-ID catalog source
    /// rather than an arbitrary symbol resolver. Unknown/ambiguous is semantic
    /// None; original-owner failure remains an outer error. Output disposal is
    /// caller-owned. This public data helper grants no proof/source authority.
    pub fn clean_cic_lineage_content_v8_observed<O: ExecutionObserver>(
        &self,
        catalog: &ModuleFunctionCatalog<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<Vec<u8>>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>())?;
        let mut state = State::default();
        let result = state.content_v8(self, catalog, &mut w);
        match result {
            Ok(true) => match w.publication() {
                Ok(()) => Ok(Some(take(&mut state.bytes))),
                Err(error) => {
                    state.retire(&mut w);
                    Err(w.terminal(error))
                }
            },
            Ok(false) => {
                state.retire(&mut w);
                w.publication()?;
                Ok(None)
            }
            Err(error) => {
                state.retire(&mut w);
                Err(w.terminal(error))
            }
        }
    }
    pub fn clean_cic_lineage_digest_v8_observed<O: ExecutionObserver>(
        &self,
        catalog: &ModuleFunctionCatalog<'_>,
        binding: Option<&CertificateBinding>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<ProofDigest>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>())?;
        let mut state = State::default();
        let result = (|| -> R<Option<ProofDigest>> {
            if !state.content_v8(self, catalog, &mut w)? {
                return Ok(None);
            }
            state.u8(u8::from(binding.is_some()), &mut w)?;
            if let Some(binding) = binding {
                state.binding(binding, &mut w)?;
            }
            Ok(Some(ProofDigest::sha256_domain_observed(
                "trust_ir.proof.clean_cic.lineage.v8",
                &state.bytes,
                w.session,
                w.site,
            )?))
        })();
        state.retire(&mut w);
        result
            .and_then(|digest| w.publication().map(|()| digest))
            .map_err(|e| w.terminal(e))
    }
}
impl ProofEvidence {
    pub fn clean_cic_lineage_binds_observed<O: ExecutionObserver>(
        &self,
        row: &ProofObligation,
        catalog: &ModuleFunctionCatalog<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 64,
            copy_bytes: size_of::<Option<ProofDigest>>(),
        })?;
        let result = if let ProofEvidence::CleanCic { lineage, .. } = self {
            let indexed = row.clean_cic_lineage_digest_observed(session, site)?;
            if *lineage == indexed {
                true
            } else {
                self.clean_cic_lineage_is_v8_observed(row, catalog, session, site)?
            }
        } else {
            false
        };
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(result)
    }
    pub fn clean_cic_lineage_is_v8_observed<O: ExecutionObserver>(
        &self,
        row: &ProofObligation,
        catalog: &ModuleFunctionCatalog<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site,
            work: 64,
            copy_bytes: size_of::<Option<ProofDigest>>(),
        })?;
        let result = if let ProofEvidence::CleanCic {
            lineage,
            kernel_recheck,
            ..
        } = self
        {
            let binding = kernel_recheck.as_ref().and_then(|r| r.binding.as_deref());
            row.clean_cic_lineage_digest_v8_observed(catalog, binding, session, site)?
                .is_some_and(|d| d == *lineage)
        } else {
            false
        };
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 1,
            copy_bytes: size_of::<bool>(),
        })?;
        Ok(result)
    }
}
impl State {
    fn index_lineage<O: ExecutionObserver>(
        &mut self,
        row: &ProofObligation,
        w: &mut Work<'_, '_, O>,
    ) -> R<ProofDigest> {
        self.u32(row.id.index(), w)?;
        self.kind(&row.kind, w)?;
        self.blob(row.description.as_bytes(), w)?;
        self.formula(row.formula.as_ref(), FormulaBindings::Tail, w)?;
        self.u8(u8::from(row.function.is_some()), w)?;
        if let Some(function) = row.function {
            self.u32(function.index(), w)?;
        }
        self.source(row.source.as_ref(), w)?;
        self.u8(u8::from(row.site.is_some()), w)?;
        if let Some(site) = row.site {
            self.u32(site.function.index(), w)?;
            self.u32(site.block.index(), w)?;
            self.u32(site.inst_index, w)?;
        }
        let bindings = row
            .formula
            .as_ref()
            .map_or(&[][..], |f| f.bindings.as_slice());
        let domain = if let Some(spec) = &row.spec {
            self.u8(1, w)?;
            self.blob(spec.machine.as_bytes(), w)?;
            self.blob(spec.temporal.as_bytes(), w)?;
            self.clauses(bindings, w)?;
            "trust_ir.proof.clean_cic.lineage.v7"
        } else if bindings.is_empty() {
            "trust_ir.proof.clean_cic.lineage.v5"
        } else {
            self.clauses(bindings, w)?;
            "trust_ir.proof.clean_cic.lineage.v6"
        };
        ProofDigest::sha256_domain_observed(domain, &self.bytes, w.session, w.site)
    }
    fn content_v8<O: ExecutionObserver>(
        &mut self,
        row: &ProofObligation,
        catalog: &ModuleFunctionCatalog<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        self.kind(&row.kind, w)?;
        self.blob(row.description.as_bytes(), w)?;
        self.formula(row.formula.as_ref(), FormulaBindings::Included, w)?;
        self.u8(u8::from(row.function.is_some()), w)?;
        if let Some(function) = row.function
            && !self.symbol(function, catalog, w)?
        {
            return Ok(false);
        }
        self.source(row.source.as_ref(), w)?;
        self.u8(u8::from(row.site.is_some()), w)?;
        if let Some(site) = row.site {
            if !self.symbol(site.function, catalog, w)? {
                return Ok(false);
            }
            self.u32(site.block.index(), w)?;
            self.u32(site.inst_index, w)?;
        }
        self.u8(u8::from(row.spec.is_some()), w)?;
        if let Some(spec) = &row.spec {
            self.blob(spec.machine.as_bytes(), w)?;
            self.blob(spec.temporal.as_bytes(), w)?;
        }
        Ok(true)
    }
    fn symbol<O: ExecutionObserver>(
        &mut self,
        id: crate::FuncId,
        catalog: &ModuleFunctionCatalog<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        if let Some(function) = catalog.unique_observed(id, w.session, w.site)? {
            self.blob(function.name.as_bytes(), w)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

impl ProofDigest {
    /// Consume an owned canonical preimage under the original caller after
    /// successful publication or sticky refusal. This is data disposal only.
    pub fn retire_canonical_bytes_observed<O: ExecutionObserver>(
        bytes: Vec<u8>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session, site };
        w.bytes(bytes);
        w.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}

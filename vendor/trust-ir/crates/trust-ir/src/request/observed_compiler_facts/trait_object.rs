// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl NativeTraitObjectMetadataFact {
    /// The complete ordinary metadata and upcast source diagnostics only.
    /// Supplied known IDs and digest bytes are checked without authenticating
    /// them or issuing source/bundle/proof authority.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        functions: &BTreeSet<FuncId>,
        obligations: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.metadata(module, self, functions, obligations, session, site);
        work.finish(result, session, site)
    }

    /// Only the original upcast source shape checks. Interior path entries
    /// remain unconstrained exactly as in that helper.
    pub fn upcast_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        let result = work.upcast(self, session, site);
        work.finish(result, session, site)
    }
}

impl Work {
    pub(super) fn metadata<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        fact: &NativeTraitObjectMetadataFact,
        functions: &BTreeSet<FuncId>,
        obligations: &BTreeSet<ProofId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::TraitObjectMetadata(fact.id);
        admit(session, site, 32, size_of::<crate::PointerLayoutShape>())?;
        if fact.ty.pointer_layout_shape(module.pointer_bits())
            != Some(crate::PointerLayoutShape::fat(
                module.pointer_bits(),
                crate::PointerMetadataShape::VTable {
                    trait_id: fact.trait_id,
                },
            ))
        {
            self.invalid(reference, "ty", session, site)?;
        }
        admit(session, site, 2, 0)?;
        if !matches!(&fact.ty, Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id }) if *trait_id == fact.trait_id)
        {
            self.invalid(reference, "trait_id", session, site)?;
        }
        if blank(&fact.vtable_symbol, session, site)? {
            self.invalid(reference, "vtable_symbol", session, site)?;
        }
        admit(session, site, 32, 0)?;
        if fact.stable_digest.is_zero() {
            self.invalid(reference, "stable_digest", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if fact.stable_digest.algorithm != crate::ProofDigestAlgorithm::Sha256 {
            self.invalid(reference, "stable_digest.algorithm", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if let Some(function) = fact.function
            && !member(functions, &function, session, site)?
        {
            self.unknown_function(reference, function, session, site)?;
        }
        self.obligations(reference, &fact.obligations, obligations, session, site)?;
        self.upcast(fact, session, site)
    }

    pub(super) fn upcast<O: ExecutionObserver>(
        &mut self,
        fact: &NativeTraitObjectMetadataFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::TraitObjectMetadata(fact.id);
        admit(session, site, 2, 0)?;
        match (fact.source_trait_id, &fact.source_ty) {
            (None, None) if fact.upcast_path.is_empty() => {}
            (Some(source), Some(ty)) => {
                admit(session, site, 2, 0)?;
                if !matches!(ty, Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id }) if *trait_id == source)
                {
                    self.invalid(reference, "source_ty", session, site)?;
                }
                admit(session, site, 1, 0)?;
                if source == fact.trait_id {
                    self.invalid(reference, "source_trait_id", session, site)?;
                }
                admit(session, site, 2, 0)?;
                if fact.upcast_path.first() != Some(&source)
                    || fact.upcast_path.last() != Some(&fact.trait_id)
                {
                    self.invalid(reference, "upcast_path", session, site)?;
                }
            }
            _ => self.invalid(reference, "upcast", session, site)?,
        }
        Ok(())
    }
}

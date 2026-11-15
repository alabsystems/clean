// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The compiler-fact constituent, never full-bundle admission or authority.

use super::*;
mod bindings;
mod collections;
mod coverage;
mod embedded;
mod facts;
mod monomorph;
#[cfg(test)]
mod tests;
mod text;
mod types;
use collections::*;

#[derive(Default)]
struct Scratch<'a> {
    functions: BTreeSet<FuncId>,
    obligations: BTreeSet<ProofId>,
    adt_ids: BTreeSet<NativeCompilerFactId>,
    fat_ids: BTreeSet<NativeCompilerFactId>,
    metadata_ids: BTreeSet<NativeCompilerFactId>,
    pointer_ids: BTreeSet<NativeCompilerFactId>,
    cast_ids: BTreeSet<NativeCompilerFactId>,
    mono_ids: BTreeSet<NativeMonomorphizationId>,
    fats: BTreeMap<NativeCompilerFactId, &'a NativeFatPointerFact>,
    metadata: BTreeMap<NativeCompilerFactId, &'a NativeTraitObjectMetadataFact>,
    pointers: BTreeMap<NativeCompilerFactId, &'a NativePointerOffsetFact>,
    casts: BTreeMap<NativeCompilerFactId, &'a NativeCastFact>,
    monos: BTreeMap<NativeMonomorphizationId, &'a NativeMonomorphizationFact>,
    digests: BTreeMap<ProofDigest, NativeMonomorphizationId>,
    // Text comparisons run explicitly in bounded chunks. No String Ord is
    // hidden in a standard map. These indexes preserve insert/replace results.
    symbols: Vec<(&'a str, NativeMonomorphizationId)>,
    public_ids: Vec<(&'a str, ProofId)>,
    mapped: BTreeSet<ProofId>,
    source_facts: BTreeSet<NativeCompilerFactRef>,
}

impl NativeVerificationBundle {
    /// Exact diagnostics of the ordinary `validate_compiler_facts`
    /// constituent, including its request/embedded-source joins. This does
    /// not run any other bundle validator, authenticate supplied identities,
    /// or confer proof/source authority. Successful result disposal is owned
    /// by the caller. Every actual query uses this original session/site.
    pub fn compiler_fact_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut work = Work::new(session, site)?;
        if let Err(error) = admit(session, site, 1, size_of::<Scratch<'_>>()) {
            return work.finish(Err(error), session, site);
        }
        let mut scratch = Scratch::default();
        let result = scratch.run(self, &mut work, session, site);
        scratch.retire(session, site);
        work.finish(result, session, site)
    }
}

impl<'a> Scratch<'a> {
    fn run<O: ExecutionObserver>(
        &mut self,
        bundle: &'a NativeVerificationBundle,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for obligation in &bundle.module.proof_obligations {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.obligations, obligation.id, session, site)? {
                work.fixed_error(
                    || E::DuplicateModuleObligationId(obligation.id),
                    session,
                    site,
                )?;
            }
        }
        for function in &bundle.module.functions {
            admit(session, site, 1, 0)?;
            set_insert(&mut self.functions, function.id, session, site)?;
        }
        let layouts = LayoutTable::new_observed(&bundle.module, session, site)?;
        let result = (|| {
            self.facts(bundle, &layouts, work, session, site)?;
            self.sources(bundle, work, session, site)?;
            self.embedded(bundle, work, session, site)
        })();
        // Observed queries keep all of their memo/scratch query-local; this
        // table's ordinary mutex memo stays empty throughout this constituent.
        session.retirement_poll(site);
        drop(layouts);
        session.retirement_poll(site);
        result?;
        admit(session, site, 1, 0)
    }

    fn sources<O: ExecutionObserver>(
        &mut self,
        bundle: &'a NativeVerificationBundle,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for source in &bundle.compiler_facts.obligation_sources {
            admit(session, site, 1, 0)?;
            self.source_header(source, work, session, site)?;
            self.source_refs(source, work, session, site)?;
            self.source_coverage(source, work, session, site)?;
            // A new set per source in the ordinary rule; retire before reuse.
            retire_set(&mut self.source_facts, session, site);
            admit(session, site, 1, 0)?;
        }
        Ok(())
    }

    fn retire<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_set(&mut self.functions, session, site);
        retire_set(&mut self.obligations, session, site);
        retire_set(&mut self.adt_ids, session, site);
        retire_set(&mut self.fat_ids, session, site);
        retire_set(&mut self.metadata_ids, session, site);
        retire_set(&mut self.pointer_ids, session, site);
        retire_set(&mut self.cast_ids, session, site);
        retire_set(&mut self.mono_ids, session, site);
        retire_map(&mut self.fats, session, site);
        retire_map(&mut self.metadata, session, site);
        retire_map(&mut self.pointers, session, site);
        retire_map(&mut self.casts, session, site);
        retire_map(&mut self.monos, session, site);
        retire_map(&mut self.digests, session, site);
        retire_vec(&mut self.symbols, session, site);
        retire_vec(&mut self.public_ids, session, site);
        retire_set(&mut self.mapped, session, site);
        retire_set(&mut self.source_facts, session, site);
    }
}

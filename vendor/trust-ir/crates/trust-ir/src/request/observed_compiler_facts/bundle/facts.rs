// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'a> Scratch<'a> {
    pub(super) fn facts<O: ExecutionObserver>(
        &mut self,
        bundle: &'a NativeVerificationBundle,
        layouts: &LayoutTable<'_>,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for fact in &bundle.compiler_facts.adt_layouts {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.adt_ids, fact.id, session, site)? {
                work.fixed_error(|| E::DuplicateCompilerFactId(fact.id), session, site)?;
            }
            let result = work.adt(layouts, fact, session, site);
            work.finish_component(result, session, site)?;
        }
        for fact in &bundle.compiler_facts.fat_pointers {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.fat_ids, fact.id, session, site)? {
                work.fixed_error(|| E::DuplicateCompilerFactId(fact.id), session, site)?;
            }
            insert(&mut self.fats, fact.id, fact, session, site)?;
            let result = work.fat_pointer(&bundle.module, fact, session, site);
            work.finish_component(result, session, site)?;
        }
        for fact in &bundle.compiler_facts.trait_object_metadata {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.metadata_ids, fact.id, session, site)? {
                work.fixed_error(|| E::DuplicateCompilerFactId(fact.id), session, site)?;
            }
            insert(&mut self.metadata, fact.id, fact, session, site)?;
            let result = work.metadata(
                &bundle.module,
                fact,
                &self.functions,
                &self.obligations,
                session,
                site,
            );
            work.finish_component(result, session, site)?;
        }
        for fact in &bundle.compiler_facts.pointer_offsets {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.pointer_ids, fact.id, session, site)? {
                work.fixed_error(|| E::DuplicateCompilerFactId(fact.id), session, site)?;
            }
            insert(&mut self.pointers, fact.id, fact, session, site)?;
            let result = work.pointer(
                layouts,
                fact,
                &self.functions,
                &self.obligations,
                session,
                site,
            );
            work.finish_component(result, session, site)?;
        }
        for fact in &bundle.compiler_facts.casts {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.cast_ids, fact.id, session, site)? {
                work.fixed_error(|| E::DuplicateCompilerFactId(fact.id), session, site)?;
            }
            insert(&mut self.casts, fact.id, fact, session, site)?;
            let result = work.cast(
                layouts,
                fact,
                &self.functions,
                &self.obligations,
                session,
                site,
            );
            work.finish_component(result, session, site)?;
        }
        for fact in &bundle.compiler_facts.monomorphizations {
            admit(session, site, 1, 0)?;
            self.monomorph(bundle, fact, work, session, site)?;
        }
        Ok(())
    }
}

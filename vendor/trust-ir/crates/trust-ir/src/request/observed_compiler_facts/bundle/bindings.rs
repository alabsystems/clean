// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
mod fact;

impl<'a> Scratch<'a> {
    pub(super) fn source_header<O: ExecutionObserver>(
        &mut self,
        source: &'a NativeObligationSource,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let obligation = source.obligation;
        if !set_insert(&mut self.mapped, obligation, session, site)? {
            work.fixed_error(|| E::DuplicateObligationSource(obligation), session, site)?;
        }
        if !member(&self.obligations, &obligation, session, site)? {
            work.fixed_error(|| E::UnknownObligationSource(obligation), session, site)?;
        }
        if !text::public_id(&source.public_obligation_id, session, site)? {
            work.fixed_error(
                || E::InvalidPublicObligationId { obligation },
                session,
                site,
            )?;
        }
        if let Some(first) = text_insert(
            &mut self.public_ids,
            &source.public_obligation_id,
            obligation,
            session,
            site,
        )? && first != obligation
        {
            work.duplicate_public(
                &source.public_obligation_id,
                first,
                obligation,
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if let Some(function) = source.function
            && !member(&self.functions, &function, session, site)?
        {
            work.fixed_error(
                || E::UnknownObligationSourceFunction {
                    obligation,
                    function,
                },
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if let Some(monomorphization) = source.monomorphization {
            if !member(&self.mono_ids, &monomorphization, session, site)? {
                work.fixed_error(
                    || E::UnknownMonomorphization {
                        obligation,
                        monomorphization,
                    },
                    session,
                    site,
                )?;
            }
            if let Some(fact) = get(&self.monos, &monomorphization, session, site)? {
                work.fact_function(
                    source,
                    NativeCompilerFactRef::Monomorphization(monomorphization),
                    fact.function,
                    session,
                    site,
                )?;
            }
        }
        self.source_set(source, work, session, site)
    }

    fn source_set<O: ExecutionObserver>(
        &mut self,
        source: &NativeObligationSource,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for fact in &source.facts {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.source_facts, *fact, session, site)? {
                work.invalid(*fact, "obligation_sources[].facts.duplicate", session, site)?;
            }
        }
        admit(session, site, 1, 0)?;
        match source.monomorphization {
            Some(id) => {
                let reference = NativeCompilerFactRef::Monomorphization(id);
                if !member(&self.source_facts, &reference, session, site)? {
                    work.invalid(
                        reference,
                        "obligation_sources[].facts.monomorphization",
                        session,
                        site,
                    )?;
                }
            }
            None => {
                admit(
                    session,
                    site,
                    observed_btree::population_work(self.source_facts.len())?,
                    0,
                )?;
                let mut facts = self.source_facts.iter();
                loop {
                    admit(
                        session,
                        site,
                        observed_btree::population_work(self.source_facts.len())?,
                        0,
                    )?;
                    let Some(fact) = facts.next() else {
                        break;
                    };
                    if matches!(fact, NativeCompilerFactRef::Monomorphization(_)) {
                        work.invalid(
                            *fact,
                            "obligation_sources[].monomorphization",
                            session,
                            site,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn source_refs<O: ExecutionObserver>(
        &self,
        source: &NativeObligationSource,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, 0)?;
        if source.cause == NativeObligationCause::CastCheck
            && !self.bound_cast(source, session, site)?
        {
            work.fixed_error(
                || E::MissingObligationSourceCastFact {
                    obligation: source.obligation,
                },
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if source.cause == NativeObligationCause::PointerOffset
            && !self.bound_pointer(source, session, site)?
        {
            work.fixed_error(
                || E::MissingObligationSourcePointerOffsetFact {
                    obligation: source.obligation,
                },
                session,
                site,
            )?;
        }
        for fact in &source.facts {
            admit(session, site, 3, 0)?;
            if let NativeCompilerFactRef::Monomorphization(actual) = fact
                && let Some(expected) = source.monomorphization
                && expected != *actual
            {
                work.fixed_error(
                    || E::ObligationSourceFactMonomorphizationMismatch {
                        obligation: source.obligation,
                        expected,
                        actual: *actual,
                    },
                    session,
                    site,
                )?;
            }
            let known = match fact {
                NativeCompilerFactRef::AdtLayout(id) => member(&self.adt_ids, id, session, site)?,
                NativeCompilerFactRef::FatPointer(id) => member(&self.fat_ids, id, session, site)?,
                NativeCompilerFactRef::TraitObjectMetadata(id) => {
                    member(&self.metadata_ids, id, session, site)?
                }
                NativeCompilerFactRef::PointerOffset(id) => {
                    member(&self.pointer_ids, id, session, site)?
                }
                NativeCompilerFactRef::Cast(id) => member(&self.cast_ids, id, session, site)?,
                NativeCompilerFactRef::Monomorphization(id) => {
                    member(&self.mono_ids, id, session, site)?
                }
            };
            if !known {
                work.fixed_error(
                    || E::UnknownCompilerFactReference {
                        obligation: source.obligation,
                        fact: *fact,
                    },
                    session,
                    site,
                )?;
            }
            self.fact_binding(source, *fact, work, session, site)?;
        }
        Ok(())
    }
}

impl Work {
    pub(super) fn fact_function<O: ExecutionObserver>(
        &mut self,
        source: &NativeObligationSource,
        fact: NativeCompilerFactRef,
        actual: Option<FuncId>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 2, 0)?;
        if let Some(actual) = actual
            && source.function != Some(actual)
        {
            self.fixed_error(
                || E::ObligationSourceFactFunctionMismatch {
                    obligation: source.obligation,
                    fact,
                    expected: source.function,
                    actual: Some(actual),
                },
                session,
                site,
            )?;
        }
        Ok(())
    }
}

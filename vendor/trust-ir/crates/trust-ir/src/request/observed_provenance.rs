// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual provenance coverage under the caller's original session and site.
//! These diagnostics grant no source, import, proof or execution authority.

use super::{NativeBundleProvenance, NativeSourceLanguage};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use crate::{FuncId, ImportId, Module, Producer};
use core::mem::{size_of, take};

mod storage;
#[cfg(test)]
mod tests;
mod validation;
use storage::*;

type R<T = ()> = Result<T, ObservedValueError>;
type FunctionRows = Vec<(Option<Producer>, Vec<FuncId>)>;
type ImportRows = Vec<(ImportId, String, Option<Producer>)>;

#[derive(Default)]
struct Functions {
    rows: FunctionRows,
    pending_producer: Option<Producer>,
    pending_ids: Vec<FuncId>,
}

#[derive(Default)]
struct Imports {
    rows: ImportRows,
    pending_name: String,
    pending_producer: Option<Producer>,
}

impl NativeBundleProvenance {
    /// The complete ordinary [`Self::uncovered_functions`] result, with the
    /// same first-producer grouping and module-order IDs. Actual variable
    /// producer comparisons, copies and storage use this original session.
    /// Resource refusal is separate from coverage. Successful caller-owned
    /// diagnostic disposal remains outside this method's observed scope.
    pub fn uncovered_functions_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<FunctionRows> {
        admit(session, site, 1, size_of::<Functions>())?;
        let mut state = Functions::default();
        let result = state.scan(self, module, session, site);
        state.finish(result, session, site)
    }

    /// The complete ordinary [`Self::uncovered_imports`] result in import
    /// table order, preserving names and `Other` identifiers verbatim. An
    /// unrepresentable uncovered import index is a resource capacity error,
    /// never a wrapped ID. Successful result disposal belongs to the caller.
    /// This observes coverage diagnostics, not dependency authentication.
    pub fn uncovered_imports_observed<O: ExecutionObserver>(
        &self,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ImportRows> {
        admit(session, site, 1, size_of::<Imports>())?;
        let mut state = Imports::default();
        let result = state.scan(self, module, session, site);
        state.finish(result, session, site)
    }
}

fn covered<O: ExecutionObserver>(
    provenance: &NativeBundleProvenance,
    producer: Option<&Producer>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    // This candidate table inspects only the enum discriminant, never Other's
    // string. It is fixed at at most two Copy-language candidates.
    admit(session, site, 2, 0)?;
    let candidates = NativeSourceLanguage::candidates_for_producer(producer);
    for language in candidates {
        admit(
            session,
            site,
            observed_btree::population_work(provenance.source_languages.len())?,
            0,
        )?;
        // NativeSourceLanguage is a finite payload-free enum. No variable
        // key comparison or unobserved string traversal occurs in this tree.
        if provenance.source_languages.contains(language) {
            return Ok(true);
        }
    }
    Ok(false)
}

impl Functions {
    fn scan<O: ExecutionObserver>(
        &mut self,
        provenance: &NativeBundleProvenance,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut index = 0;
        while index < module.functions.len() {
            admit(session, site, 1, 0)?;
            let function = &module.functions[index];
            let producer = function.producer.as_ref();
            if !covered(provenance, producer, session, site)? {
                self.function(producer, function.id, session, site)?;
            }
            index += 1;
        }
        Ok(())
    }

    fn function<O: ExecutionObserver>(
        &mut self,
        producer: Option<&Producer>,
        id: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut group = 0;
        while group < self.rows.len() {
            admit(session, site, 1, 0)?;
            if producer_equal(self.rows[group].0.as_ref(), producer, session, site)? {
                return push_id(&mut self.rows[group].1, id, session, site);
            }
            group += 1;
        }
        reserve(&mut self.rows, session, site)?;
        self.pending_producer = copy_producer(producer, session, site)?;
        push_id(&mut self.pending_ids, id, session, site)?;
        admit(
            session,
            site,
            1,
            size_of::<(Option<Producer>, Vec<FuncId>)>(),
        )?;
        self.rows
            .push((self.pending_producer.take(), take(&mut self.pending_ids)));
        Ok(())
    }

    fn retire_pending<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_producer(self.pending_producer.take(), session, site);
        retire_ids(&mut self.pending_ids, session, site);
    }

    fn retire_rows<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        while !self.rows.is_empty() {
            session.retirement_poll(site);
            if let Some((producer, mut ids)) = self.rows.pop() {
                retire_producer(producer, session, site);
                retire_ids(&mut ids, session, site);
            }
        }
        retire_value(take(&mut self.rows), session, site);
    }

    fn finish<O: ExecutionObserver>(
        mut self,
        result: R,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<FunctionRows> {
        self.retire_pending(session, site);
        if let Err(error) = result {
            self.retire_rows(session, site);
            return Err(terminal(error, session));
        }
        if let Err(error) = publication(session, site) {
            self.retire_rows(session, site);
            return Err(terminal(error, session));
        }
        Ok(take(&mut self.rows))
    }
}

impl Imports {
    fn scan<O: ExecutionObserver>(
        &mut self,
        provenance: &NativeBundleProvenance,
        module: &Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut index = 0;
        while index < module.imports.len() {
            admit(session, site, 1, 0)?;
            let import = &module.imports[index];
            if !covered(provenance, import.producer.as_ref(), session, site)? {
                let id = checked_import_id(index, session, site)?;
                reserve(&mut self.rows, session, site)?;
                self.pending_name = copy_text(&import.name, session, site)?;
                self.pending_producer = copy_producer(import.producer.as_ref(), session, site)?;
                admit(
                    session,
                    site,
                    1,
                    size_of::<(ImportId, String, Option<Producer>)>(),
                )?;
                self.rows.push((
                    id,
                    take(&mut self.pending_name),
                    self.pending_producer.take(),
                ));
            }
            index += 1;
        }
        Ok(())
    }

    fn retire_pending<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_value(take(&mut self.pending_name), session, site);
        retire_producer(self.pending_producer.take(), session, site);
    }

    fn retire_rows<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        while !self.rows.is_empty() {
            session.retirement_poll(site);
            if let Some((_, name, producer)) = self.rows.pop() {
                retire_value(name, session, site);
                retire_producer(producer, session, site);
            }
        }
        retire_value(take(&mut self.rows), session, site);
    }

    fn finish<O: ExecutionObserver>(
        mut self,
        result: R,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ImportRows> {
        self.retire_pending(session, site);
        if let Err(error) = result {
            self.retire_rows(session, site);
            return Err(terminal(error, session));
        }
        if let Err(error) = publication(session, site) {
            self.retire_rows(session, site);
            return Err(terminal(error, session));
        }
        Ok(take(&mut self.rows))
    }
}

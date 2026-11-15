// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Observe the actual duplicate-aware function-index construction, not a
//! speculative prewalk. This index grants no proof or validation authority.

use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use crate::{Module, ModuleFunctionCatalog, ModuleFunctionState};
use core::mem::size_of;
use std::collections::{BTreeMap, btree_map::Entry};

impl<'module> ModuleFunctionCatalog<'module> {
    /// The exact immutable source indexed here. This is not a validated-module
    /// capability; callers must still run their complete original validator.
    pub fn source_module(&self) -> &'module Module {
        self.module
    }

    /// Index the same exact immutable declarations as [`Self::new`], observing
    /// the caller's existing operation before each actual lookup/insertion.
    ///
    /// `site` identifies the original requesting operation; declaration visits
    /// identify their actual function IDs. The same borrowed session retains
    /// the first typed refusal. No partial catalog is returned after a stop.
    /// Requested B-tree storage uses the same sealed-library upper bound as
    /// observed reference execution, not an allocator/RSS or latency promise.
    /// Failed construction retires its map with original-owner polls; successful
    /// output and its later disposal remain the caller's responsibility.
    pub fn new_observed<O: ExecutionObserver>(
        module: &'module Module,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Self, ObservedValueError> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::ModuleLookup,
            site,
            work: 1,
            copy_bytes: size_of::<Self>(),
        })?;
        let mut entries = BTreeMap::new();
        let result = (|| {
            for function in &module.functions {
                let cost = observed_btree::insertion_cost::<u32, ModuleFunctionState<'module>>(
                    entries.len(),
                )?;
                session.admit(ExecutionProgress {
                    phase: ExecutionPhase::ModuleLookup,
                    site: ExecutionSite::Entry(function.id),
                    work: cost.work,
                    copy_bytes: cost.copy_bytes,
                })?;
                // Prepayment includes the entry search and its complete possible
                // split/root work. Repeated IDs become permanently ambiguous.
                match entries.entry(function.id.index()) {
                    Entry::Vacant(entry) => {
                        entry.insert(ModuleFunctionState::Unique(function));
                    }
                    Entry::Occupied(mut entry) => {
                        entry.insert(ModuleFunctionState::Ambiguous);
                    }
                }
            }
            Ok::<(), ObservedValueError>(())
        })();
        finish_catalog(module, entries, result, session, site)
    }
}

fn finish_catalog<'module, O: ExecutionObserver>(
    module: &'module Module,
    mut entries: BTreeMap<u32, ModuleFunctionState<'module>>,
    result: Result<(), ObservedValueError>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<ModuleFunctionCatalog<'module>, ObservedValueError> {
    let result = result.and_then(|()| {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })?;
        Ok(())
    });
    if let Err(error) = result {
        // Insertion prepayment includes eventual B-tree retirement. Do not
        // hide an unbounded population walk inside an implicit map Drop.
        while !entries.is_empty() {
            session.retirement_poll(site);
            entries.pop_first();
        }
        session.retirement_poll(site);
        drop(entries);
        // Preserve an already held local error. The same original session
        // independently retains its first refusal during consuming cleanup.
        return Err(error);
    }
    Ok(ModuleFunctionCatalog { module, entries })
}

#[cfg(test)]
mod tests;

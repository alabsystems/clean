// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual closed catalog query/cursor/retirement under its caller's owner.
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use crate::{FuncId, Function, ModuleFunctionCatalog, ModuleFunctionState};
use core::mem::size_of;
use std::collections::{BTreeMap, btree_map::Iter};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
impl<'module> ModuleFunctionCatalog<'module> {
    /// Read this actual immutable catalog only. Sparse IDs and permanent
    /// ambiguity have exactly `unique`'s meaning; an operational refusal never
    /// becomes semantic None. Fixed-u32 tree work is prepaid with existing core
    /// logical bounds before the actual primitive, in the same session/site.
    /// This returns borrowed data, never a declaration/module/source capability.
    pub fn unique_observed<O: ExecutionObserver>(
        &self,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<&'module Function>> {
        let mut work = Work { session, site };
        work.lookup(self.entries.len())?;
        work.admit(1, size_of::<Option<&Function>>())?;
        let output = match self.entries.get(&function.index()) {
            Some(ModuleFunctionState::Unique(function)) => Some(*function),
            Some(ModuleFunctionState::Ambiguous) | None => None,
        };
        work.publication(size_of::<Option<&Function>>())?;
        Ok(output)
    }
    /// Enumerate this exact catalog's ambiguous IDs in original numeric order.
    /// Each actual cursor advance and output growth is observed, including when
    /// no ambiguous row exists. Full partial output stays held until transfer or
    /// explicit original-session retirement. No authority or fresh grant issued.
    pub fn ambiguous_ids_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<u32>> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Vec<u32>>())?;
        let mut output = Vec::new();
        let result = self.ambiguous(&mut output, &mut work);
        work.finish_roster(result, output)
    }
    fn ambiguous<O: ExecutionObserver>(
        &self,
        output: &mut Vec<u32>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.lookup(self.entries.len())?;
        work.admit(1, size_of::<Iter<'_, u32, ModuleFunctionState<'_>>>())?;
        let mut rows = self.entries.iter();
        loop {
            work.lookup(self.entries.len())?;
            work.admit(1, size_of::<Option<(&u32, &ModuleFunctionState<'_>)>>())?;
            let Some((id, state)) = rows.next() else {
                break;
            };
            work.admit(1, size_of::<bool>())?;
            if matches!(state, ModuleFunctionState::Ambiguous) {
                work.reserve(output)?;
                work.admit(1, size_of::<u32>())?;
                output.push(*id);
            }
        }
        Ok(())
    }
    /// Consume all actual Copy-valued tree rows/buffers despite sticky refusal.
    /// Only borrowed declarations are in the map; original Module disposal is
    /// still caller-owned. Healthy terminal Publication(0,0) is the stop check;
    /// no normal output is published once the original session has stopped.
    /// Logical standard-library pricing grants no allocator/deallocator/OOM,
    /// panic/unwind/RSS/callback or hard-time guarantee.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.step(size_of::<Self>() + 1);
        let Self {
            module: _,
            mut entries,
        } = self;
        loop {
            work.step(
                entries
                    .len()
                    .saturating_add(1)
                    .saturating_add(size_of::<Option<(u32, ModuleFunctionState<'_>)>>()),
            );
            if entries.pop_first().is_none() {
                break;
            }
            work.poll();
        }
        work.step(size_of::<BTreeMap<u32, ModuleFunctionState<'_>>>() + 1);
        drop(entries);
        work.poll();
        work.publication(0)
    }
}

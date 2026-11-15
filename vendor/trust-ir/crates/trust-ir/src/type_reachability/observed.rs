// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual nominal table graph and three-axis fixpoint under one original owner.
use super::{AXES, NominalAxis, TableReferent, seeds, table_referent};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{Inst, Module, Ty};
use core::mem::{size_of, take};
mod builder;
mod inventory;
mod query;
mod storage;
mod tables;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
use tables::{Bounds, Tables};
use walk::Inline;
type R<T = ()> = Result<T, ObservedValueError>;
const NO_EDGE: usize = usize::MAX;
#[derive(Clone, Copy)]
struct ReverseEdge {
    dependent: usize,
    next: usize,
}
/// Exact nominal reachability data borrowing the module it describes. Actual
/// graph construction, propagation, queries and explicit retirement use the
/// caller's original session/site; no owner, deadline, fuel or grant is made.
///
/// Named indexes use paid first-match physical pair scans instead of opaque
/// hash-map construction/rehashing. Duplicate IDs combine every definition at
/// the original first vertex. This can be quadratic and is budget-refusable;
/// runtime cost is UNMEASURED. No representation/module/source/proof authority
/// is established. Physical std/allocator/deallocator/OOM/panic/unwind/RSS/
/// hard-time containment and disposal of original inputs remain OPEN. Callers
/// must keep this summary in original custody and explicitly retire it.
pub struct ObservedNominalTypeReachability<'module> {
    _module: &'module Module,
    tables: Tables,
    reachable: [Vec<bool>; 3],
}
struct State<'module> {
    summary: ObservedNominalTypeReachability<'module>,
    heads: Vec<usize>,
    edges: Vec<ReverseEdge>,
    pending: [Vec<usize>; 3],
    inline: Inline<'module>,
}
impl Module {
    /// Construct the actual ordinary nominal graph and all three least
    /// fixpoints. Every source row/inline occurrence/reverse edge/worklist
    /// operation is observed inside the traversal. Missing references add no
    /// edge exactly as before; separate mandatory validation still rejects
    /// them. No opaque ordinary prewalk or successful summary is substituted
    /// on stop. Complete partial graph/index/bitset state is held and retired.
    pub fn nominal_type_reachability_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ObservedNominalTypeReachability<'_>> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State {
            summary: ObservedNominalTypeReachability {
                _module: self,
                tables: Tables::default(),
                reachable: [Vec::new(), Vec::new(), Vec::new()],
            },
            heads: Vec::new(),
            edges: Vec::new(),
            pending: [Vec::new(), Vec::new(), Vec::new()],
            inline: Inline::default(),
        };
        let result = state.construct(self, &mut work);
        state.retire_builder(&mut work);
        match result
            .and_then(|()| work.publication(size_of::<ObservedNominalTypeReachability<'_>>()))
        {
            Ok(()) => Ok(state.summary),
            Err(error) => {
                state.summary.retire(&mut work);
                Err(work.terminal(error))
            }
        }
    }
}
impl ObservedNominalTypeReachability<'_> {
    /// Consume every retained pair/bitset under original sticky retirement.
    /// A refusal never stops draining the remaining owned stores.
    pub fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.retire(&mut work);
        work.publication(0)
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_copy(&mut self.tables.structs);
        work.retire_copy(&mut self.tables.enums);
        work.retire_copy(&mut self.tables.records);
        for axis in AXES {
            work.step(1);
            work.retire_copy(&mut self.reachable[axis as usize]);
        }
        work.step(size_of::<Tables>() + size_of::<&Module>());
        work.poll();
    }
}
impl State<'_> {
    fn retire_builder<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.inline.retire(work);
        work.retire_copy(&mut self.heads);
        work.retire_copy(&mut self.edges);
        for axis in AXES {
            work.step(1);
            work.retire_copy(&mut self.pending[axis as usize]);
        }
        work.poll();
    }
}

impl<'module> ObservedNominalTypeReachability<'module> {
    /// Exact original borrowed module behind these data-only reachability
    /// facts. Identity is not a validity/proof/source-authentication capability.
    pub fn source_module(&self) -> &'module Module {
        self._module
    }
}

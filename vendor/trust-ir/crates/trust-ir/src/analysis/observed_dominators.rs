// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual Cooper/Harvey/Kennedy construction and queries under one borrowed
//! caller session. Only fixed-key maps and borrowed edge headers are used.
//! No ordinary constructor/query, proof authority or fresh owner is credited.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::{size_of, take};

mod build;
mod iteration;
mod queries;
mod solve;
mod storage;
#[cfg(test)]
mod tests;

type R<T = ()> = Result<T, ObservedValueError>;

struct Work<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
}

#[derive(Default)]
struct State<'f> {
    tree: DominatorTree,
    blocks: BTreeSet<u32>,
    successors: BTreeMap<u32, Vec<u32>>,
    predecessors: BTreeMap<u32, Vec<u32>>,
    children: BTreeMap<u32, Vec<u32>>,
    rpo_number: BTreeMap<u32, usize>,
    edge_entries: BTreeMap<u32, Option<(u32, usize)>>,
    rpo: Vec<u32>,
    frames: Vec<(u32, usize)>,
    targets: Vec<u32>,
    edges: Vec<crate::Edge<'f>>,
}

impl DominatorTree {
    /// Construct the exact ordinary analysis. Malformed CFGs return the same
    /// empty fail-closed tree; resource/refusal errors return no partial tree.
    /// The caller supplies its original session/site. This establishes no SSA
    /// uniqueness, function validity or source/proof authority. Successful
    /// output disposal and physical allocator/panic/time bounds are separate.
    pub fn new_observed<O: ExecutionObserver>(
        function: &Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.build(function, &mut work);
        state.retire_scratch(&mut work);
        match result {
            Ok(valid) => {
                if !valid {
                    state.retire_tree(&mut work);
                }
                if work.publication(size_of::<Self>()).is_err() {
                    state.retire_tree(&mut work);
                    return Err(ObservedValueError::AdmissionRefused);
                }
                Ok(take(&mut state.tree))
            }
            Err(error) => {
                state.retire_tree(&mut work);
                Err(work.terminal(error))
            }
        }
    }

    /// Retire all owned analysis maps under the same original session, even
    /// after it has stopped. The final check cannot renew a stopped operation.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.session.retirement_step(site, 1);
        let mut state = State {
            tree: self,
            ..State::default()
        };
        state.retire_tree(&mut work);
        work.publication(0)
    }
}

impl State<'_> {
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_set(&mut self.blocks);
        work.retire_rows(&mut self.successors);
        work.retire_rows(&mut self.predecessors);
        work.retire_rows(&mut self.children);
        work.retire_map(&mut self.rpo_number);
        work.retire_map(&mut self.edge_entries);
        work.retire_vec(take(&mut self.rpo));
        work.retire_vec(take(&mut self.frames));
        work.retire_vec(take(&mut self.targets));
        work.retire_vec(take(&mut self.edges));
    }
    fn retire_tree<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.tree.well_formed = false;
        work.retire_set(&mut self.tree.reachable);
        work.retire_map(&mut self.tree.immediate_dominator);
        work.retire_map(&mut self.tree.preorder);
        work.retire_map(&mut self.tree.postorder);
        work.retire_map(&mut self.tree.instruction_counts);
        work.retire_map(&mut self.tree.invoke_instructions);
        work.retire_map(&mut self.tree.dominating_edges);
    }
}

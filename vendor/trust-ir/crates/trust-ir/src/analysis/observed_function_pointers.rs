// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual lazy typed static-pointer analysis under the original caller session.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::{size_of, take};
use std::collections::btree_map::Iter;
mod definitions;
mod prefilter;
mod provenance;
mod resolve;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod use_sites;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Immutable original Function, with lazily derived private caches. Results
/// have exactly the ordinary typed resolver's meaning: ephemeral local DATA,
/// not declaration/signature/source/proof authority. The module consumer must
/// immediately check the exact unique declaration and complete signature.
/// No constructor accepts candidate caches or another function's facts.
#[derive(Debug)]
pub struct ObservedStaticFunctionPointerAnalysis<'f> {
    function: &'f Function,
    state: State<'f>,
}
#[derive(Debug, Default)]
struct State<'f> {
    use_built: bool,
    definitions_built: bool,
    provenance_built: bool,
    uses: BTreeMap<u32, UseBlockState<'f>>,
    definitions: BTreeMap<u32, DefinitionState<'f>>,
    provenances: BTreeMap<u32, ProvenanceState<'f>>,
    dominators: Option<DominatorTree>,
    pending_use: Option<UseBlockState<'f>>,
    old_use: Option<UseBlockState<'f>>,
    active: BTreeSet<u32>,
    path: Vec<(u32, ProvenanceStep<'f>)>,
}
impl<'f> ObservedStaticFunctionPointerAnalysis<'f> {
    /// Borrow only; do not eagerly build any whole-function component.
    pub fn new_observed<O: ExecutionObserver>(
        function: &'f Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Self>() + size_of::<Work<'_, '_, O>>())?;
        let out = Self {
            function,
            state: State::default(),
        };
        if let Err(error) = work.publication(size_of::<Self>()) {
            out.retire_inner(&mut work);
            return Err(work.terminal(error));
        }
        Ok(out)
    }
    /// Fixed-size informational snapshot; reading it initializes nothing.
    #[must_use]
    pub fn cache_state(&self) -> StaticFunctionPointerCacheState {
        StaticFunctionPointerCacheState {
            use_site_index_built: self.state.use_built,
            definition_index_built: self.state.definitions_built,
            provenance_index_built: self.state.provenance_built,
            dominator_tree_built: self.state.dominators.is_some(),
        }
    }
    /// Authenticate the actual node/use, definitions, CFG and every candidate
    /// provenance edge in ordinary order. All actual work/allocation uses the
    /// supplied original session/site; no fresh grant/deadline/TLS/fuel. Any
    /// operational refusal drains ALL partial/prior caches and cannot become
    /// semantic None or a shorter accepting path. Successful caches are held
    /// until the caller explicitly consumes this analysis with retire_observed.
    /// Logical std pricing is not a physical allocator/OOM/panic/RSS/callback
    /// or hard-time bound; original input disposal remains caller-owned.
    pub fn resolve_typed_at_observed<O: ExecutionObserver>(
        &mut self,
        value: ValueId,
        use_block: BlockId,
        use_instruction_index: usize,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<StaticFunctionPointerResolution>> {
        let mut work = Work { session, site };
        let answer = resolve::run(
            self.function,
            &mut self.state,
            value,
            use_block,
            use_instruction_index,
            &mut work,
        );
        match answer.and_then(|answer| {
            work.publication(size_of::<Option<StaticFunctionPointerResolution>>())?;
            Ok(answer)
        }) {
            Ok(answer) => Ok(answer),
            Err(error) => {
                self.state.retire(&mut work);
                Err(work.terminal(error))
            }
        }
    }
    /// Consume every retained cache/buffer, including stopped sessions.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.retire_inner(&mut work);
        work.publication(0)
    }
    fn retire_inner<O: ExecutionObserver>(mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Self>() + 1);
        self.state.retire(work);
    }
}

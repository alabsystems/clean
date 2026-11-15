// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The actual pool-closing algorithm under the original observation session.
//! This computes pool facts only; it grants no validation or proof authority.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::size_of;

mod closure;
mod keys;
mod rows;
mod storage;
#[cfg(test)]
mod tests;

use keys::{Key, Row};
use storage::*;

type Observed<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct Closing<'a> {
    adjacency: BTreeMap<PrincipalKey, BTreeSet<PrincipalKey>>,
    starts: Vec<PrincipalKey>,
    pending: Vec<PrincipalKey>,
    reached: BTreeSet<PrincipalKey>,
    erased: BTreeSet<PrincipalKey>,
    demoted: BTreeSet<PrincipalKey>,
    rows: Vec<Row<'a>>,
    row_scratch: Vec<Row<'a>>,
    recorded: BTreeSet<PrincipalKey>,
    opened: BTreeSet<PrincipalKey>,
    shape_prefixes: BTreeSet<(Option<u32>, Option<bool>)>,
    pending_key: Option<PoolKey>,
    pending_carried: Option<CarriedKey>,
    output: ClosedPools,
}

impl IndirectCallUniverse {
    /// Close the original facts with admission in the real closure loops.
    ///
    /// The retained `laundered_keys` B-tree still uses standard derived Ord.
    /// Two nonempty Fn parameter keys with the same ABI/variadic prefix are
    /// refused before their insertion could compare variable-length params.
    /// No incomplete pools are returned. Allocator latency is not bounded by
    /// logical requested-storage prepayment; successful disposal is caller-owned.
    pub(crate) fn close_observed<O: ExecutionObserver>(
        &self,
        unenumerated: bool,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<ClosedPools> {
        admit(session, site, 1, size_of::<Closing<'_>>())?;
        let mut closing = Closing::default();
        let result = closing.run(self, unenumerated, session, site);
        closing.retire_scratch(session, site);
        if let Err(error) = result {
            closing.retire_output(session, site);
            return Err(if session.first_refusal().is_some() {
                ObservedValueError::AdmissionRefused
            } else {
                error
            });
        }
        if session.first_refusal().is_some() {
            closing.retire_output(session, site);
            return Err(ObservedValueError::AdmissionRefused);
        }
        if session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            })
            .is_err()
        {
            closing.retire_output(session, site);
            return Err(ObservedValueError::AdmissionRefused);
        }
        Ok(core::mem::take(&mut closing.output))
    }
}

impl<'a> Closing<'a> {
    fn run<O: ExecutionObserver>(
        &mut self,
        universe: &'a IndirectCallUniverse,
        unenumerated: bool,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        self.upcasts(universe, session, site)?;
        let mut launders_any_dyn = false;
        for key in universe.laundered.keys() {
            admit(session, site, 1, 0)?;
            launders_any_dyn |= matches!(key, CarriedKey::Any | CarriedKey::AnyDyn);
            if let Some(principal) = key.principal() {
                insert(&mut self.erased, principal, session, site)?;
            }
        }
        for principal in &universe.erased {
            admit(session, site, 1, 0)?;
            insert(&mut self.erased, *principal, session, site)?;
        }
        closure::extend(
            &self.erased,
            &self.output.upcast_reach,
            &mut self.demoted,
            session,
            site,
        )?;
        self.members(universe, launders_any_dyn, session, site)?;
        self.open_principals(universe, session, site)?;
        self.copy_launders(universe, session, site)?;
        admit(session, site, 1, size_of::<ClosedPools>())?;
        self.output.launder = universe.launder;
        self.output.unclosed = unenumerated || !self.output.open.is_empty();
        Ok(())
    }

    fn retire_scratch<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_map_sets(&mut self.adjacency, session, site);
        retire_vec(&mut self.starts, session, site);
        retire_vec(&mut self.pending, session, site);
        retire_set(&mut self.reached, session, site);
        retire_set(&mut self.erased, session, site);
        retire_set(&mut self.demoted, session, site);
        retire_vec(&mut self.rows, session, site);
        retire_vec(&mut self.row_scratch, session, site);
        retire_set(&mut self.recorded, session, site);
        retire_set(&mut self.opened, session, site);
        retire_set(&mut self.shape_prefixes, session, site);
    }

    fn retire_output<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_value(self.pending_key.take(), session, site);
        retire_value(self.pending_carried.take(), session, site);
        while !self.output.members.is_empty() {
            session.retirement_poll(site);
            let value = self.output.members.pop();
            retire_value(value, session, site);
        }
        retire_vec(&mut self.output.members, session, site);
        while !self.output.laundered.is_empty() {
            session.retirement_poll(site);
            let value = self.output.laundered.pop_first();
            retire_value(value, session, site);
        }
        retire_set(&mut self.output.open, session, site);
        retire_map_sets(&mut self.output.upcast_reach, session, site);
    }
}

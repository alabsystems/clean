// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn rows<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>() + 1);
            if rows.pop().is_none() {
                break;
            }
            self.poll();
        }
        self.step(size_of::<Vec<T>>() + 1);
        drop(rows);
        self.poll();
    }
    pub(super) fn map<V: Copy>(&mut self, map: &mut BTreeMap<u32, V>) {
        loop {
            self.step(
                map.len()
                    .saturating_add(1)
                    .saturating_add(size_of::<Option<(u32, V)>>()),
            );
            if map.pop_first().is_none() {
                break;
            }
            self.poll();
        }
        self.step(size_of::<BTreeMap<u32, V>>() + 1);
        drop(take(map));
        self.poll();
    }
    pub(super) fn set(&mut self, set: &mut BTreeSet<u32>) {
        loop {
            self.step(
                set.len()
                    .saturating_add(1)
                    .saturating_add(size_of::<Option<u32>>()),
            );
            if set.pop_first().is_none() {
                break;
            }
            self.poll();
        }
        self.step(size_of::<BTreeSet<u32>>() + 1);
        drop(take(set));
        self.poll();
    }
    pub(super) fn use_state(&mut self, state: Option<UseBlockState<'_>>) {
        self.step(size_of::<Option<UseBlockState<'_>>>() + 1);
        if let Some(UseBlockState::Unique {
            block: _,
            mut parameters,
        }) = state
        {
            self.set(&mut parameters);
        }
        self.poll();
    }
}
impl State<'_> {
    pub(super) fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<State<'_>>() + 1);
        self.use_built = false;
        self.definitions_built = false;
        self.provenance_built = false;
        work.use_state(self.pending_use.take());
        work.use_state(self.old_use.take());
        loop {
            work.step(
                self.uses
                    .len()
                    .saturating_add(1)
                    .saturating_add(size_of::<Option<(u32, UseBlockState<'_>)>>()),
            );
            let Some((_, state)) = self.uses.pop_first() else {
                break;
            };
            work.use_state(Some(state));
        }
        work.step(size_of::<BTreeMap<u32, UseBlockState<'_>>>() + 1);
        drop(take(&mut self.uses));
        work.poll();
        work.map(&mut self.definitions);
        work.map(&mut self.provenances);
        work.set(&mut self.active);
        work.rows(take(&mut self.path));
        work.step(size_of::<Option<DominatorTree>>() + 1);
        if let Some(tree) = self.dominators.take() {
            // Child consumes all actual maps even when already stopped.
            let _ = tree.retire_observed(work.session, work.site);
        }
        work.poll();
    }
}

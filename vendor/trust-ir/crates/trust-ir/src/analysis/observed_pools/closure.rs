// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Closing<'_> {
    pub(super) fn upcasts<O: ExecutionObserver>(
        &mut self,
        universe: &IndirectCallUniverse,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        for (from, to) in &universe.upcasts {
            admit(session, site, 1, 0)?;
            if from == to {
                continue;
            }
            lookup(self.adjacency.len(), session, site)?;
            if !self.adjacency.contains_key(from) {
                tree_growth::<PrincipalKey, BTreeSet<PrincipalKey>, O>(
                    self.adjacency.len(),
                    session,
                    site,
                )?;
                self.adjacency.insert(*from, BTreeSet::new());
            }
            lookup(self.adjacency.len(), session, site)?;
            let Some(targets) = self.adjacency.get_mut(from) else {
                return Err(ObservedValueError::InvalidRange);
            };
            insert(targets, *to, session, site)?;
        }
        for start in self.adjacency.keys() {
            push(&mut self.starts, *start, session, site)?;
        }
        for position in 0..self.starts.len() {
            admit(session, site, 1, 0)?;
            self.reach_start(self.starts[position], session, site)?;
        }
        Ok(())
    }

    fn reach_start<O: ExecutionObserver>(
        &mut self,
        start: PrincipalKey,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        lookup(self.adjacency.len(), session, site)?;
        if let Some(targets) = self.adjacency.get(&start) {
            for target in targets {
                push(&mut self.pending, *target, session, site)?;
            }
        }
        while !self.pending.is_empty() {
            admit(session, site, 1, 0)?;
            let Some(next) = self.pending.pop() else {
                break;
            };
            if !insert(&mut self.reached, next, session, site)? {
                continue;
            }
            lookup(self.adjacency.len(), session, site)?;
            if let Some(targets) = self.adjacency.get(&next) {
                for target in targets {
                    push(&mut self.pending, *target, session, site)?;
                }
            }
        }
        lookup(self.reached.len(), session, site)?;
        self.reached.remove(&start);
        tree_growth::<PrincipalKey, BTreeSet<PrincipalKey>, O>(
            self.output.upcast_reach.len(),
            session,
            site,
        )?;
        self.output
            .upcast_reach
            .insert(start, core::mem::take(&mut self.reached));
        Ok(())
    }

    pub(super) fn open_principals<O: ExecutionObserver>(
        &mut self,
        universe: &IndirectCallUniverse,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        for member in &self.output.members {
            admit(session, site, 1, 0)?;
            if let Some(principal) = member.key.principal() {
                insert(&mut self.recorded, principal, session, site)?;
            }
        }
        for (from, to) in &universe.upcasts {
            admit(session, site, 1, 0)?;
            if from != to && !contains(&self.recorded, from, session, site)? {
                insert(&mut self.opened, *to, session, site)?;
            }
        }
        for invoke in &universe.invokes {
            admit(session, site, 1, 0)?;
            self.name(invoke.key.principal(), session, site)?;
            for key in &invoke.carried {
                admit(session, site, 1, 0)?;
                self.name(key.principal(), session, site)?;
            }
        }
        for handoff in &universe.handoffs {
            admit(session, site, 1, 0)?;
            for key in &handoff.carried {
                admit(session, site, 1, 0)?;
                self.name(key.principal(), session, site)?;
            }
        }
        for key in universe.laundered.keys() {
            admit(session, site, 1, 0)?;
            self.name(key.principal(), session, site)?;
        }
        extend(
            &self.opened,
            &self.output.upcast_reach,
            &mut self.output.open,
            session,
            site,
        )
    }

    fn name<O: ExecutionObserver>(
        &mut self,
        principal: Option<PrincipalKey>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        if let Some(principal) = principal
            && !contains(&self.recorded, &principal, session, site)?
        {
            insert(&mut self.opened, principal, session, site)?;
        }
        Ok(())
    }
}

pub(super) fn extend<O: ExecutionObserver>(
    seeds: &BTreeSet<PrincipalKey>,
    reach: &BTreeMap<PrincipalKey, BTreeSet<PrincipalKey>>,
    output: &mut BTreeSet<PrincipalKey>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    for seed in seeds {
        admit(session, site, 1, 0)?;
        insert(output, *seed, session, site)?;
    }
    for seed in seeds {
        lookup(reach.len(), session, site)?;
        if let Some(reached) = reach.get(seed) {
            for principal in reached {
                admit(session, site, 1, 0)?;
                insert(output, *principal, session, site)?;
            }
        }
    }
    Ok(())
}

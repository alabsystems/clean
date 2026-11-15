// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Observed traversal of an already constructed and solved reachability census.
//! Graph construction, pool derivation and certificate checking are not covered.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::size_of;

#[cfg(test)]
mod tests;

impl ReachCensus {
    /// The exact ordinary thread closure, with inner work/storage admission.
    ///
    /// `site` names the caller's actual operation. This borrows its original
    /// session and consumes no interpreter fuel. Refusal returns no partial
    /// closure. Local scratch is retired before the final publication poll;
    /// successful output and its later disposal remain caller-owned data.
    /// Requested storage/copy prepayment is not allocator, RSS or OOM authority.
    pub fn thread_closure_observed<O: ExecutionObserver>(
        &self,
        entry: Option<ReachNode>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ThreadClosure, ObservedValueError> {
        admit(session, site, 0, 0)?;
        let graph = &self.graph;
        let mut reached = BTreeMap::new();
        let mut scratch = Scratch::default();
        let result = (|| {
            admit(session, site, 1, size_of::<ThreadClosure>())?;
            let Some(start) = entry.filter(|node| {
                graph
                    .local(*node)
                    .is_some_and(|index| !graph.is_hub_index(index))
            }) else {
                return Ok(false);
            };
            scratch.build(graph, session, site)?;
            insert(&mut reached, start, None, session, site)?;
            push(&mut scratch.queue, start, session, site)?;
            graph.extend_closure(&mut scratch, &mut reached, session, site)?;
            self.closure_modelable(&scratch.param, &reached, session, site)
        })();
        scratch.retire(session, site);
        let result = result.and_then(|modelable| {
            session.admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            })?;
            Ok(modelable)
        });
        match result {
            Ok(modelable) => Ok(ThreadClosure {
                entry,
                reached,
                modelable,
            }),
            Err(error) => {
                // Each B-tree insertion prepaid eventual removal/retirement.
                while !reached.is_empty() {
                    session.retirement_poll(site);
                    reached.pop_first();
                }
                session.retirement_poll(site);
                drop(reached);
                if session.first_refusal().is_some() {
                    Err(ObservedValueError::AdmissionRefused)
                } else {
                    Err(error)
                }
            }
        }
    }

    fn closure_modelable<O: ExecutionObserver>(
        &self,
        param: &[bool],
        reached: &BTreeMap<ReachNode, Option<ReachEdge>>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<bool, ObservedValueError> {
        admit(session, site, 1, 0)?;
        if self.fallback.is_some() {
            return Ok(false);
        }
        admit(
            session,
            site,
            observed_btree::population_work(reached.len())?,
            0,
        )?;
        let mut nodes = reached.keys();
        loop {
            admit(
                session,
                site,
                observed_btree::population_work(reached.len())?,
                0,
            )?;
            let Some(node) = nodes.next() else { break };
            let index = node.index();
            if param[index]
                || matches!(self.verdict(*node), Verdict::Unknown | Verdict::Indirect)
                || !matches!(
                    self.graph.nodes[index],
                    ReachNodeKind::Program(ReachNodeSpec {
                        body: NodeBody::Walked | NodeBody::Seed | NodeBody::Primitive,
                        ..
                    })
                )
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[derive(Default)]
struct Scratch {
    outgoing: Vec<Vec<usize>>,
    param: Vec<bool>,
    spent: Vec<bool>,
    // A cursor preserves VecDeque's BFS order. Retained popped entries are
    // bounded by the actual reached population and are explicitly prepaid.
    queue: Vec<ReachNode>,
}

impl Scratch {
    fn build<O: ExecutionObserver>(
        &mut self,
        graph: &ExpandedReachGraph,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<(), ObservedValueError> {
        for _ in &graph.nodes {
            admit(session, site, 1, 0)?;
            push(&mut self.outgoing, Vec::new(), session, site)?;
            push(&mut self.param, false, session, site)?;
        }
        for (index, edge) in graph.edges[..graph.base_edges].iter().enumerate() {
            admit(session, site, 1, 0)?;
            match edge.class {
                EdgeClass::Run | EdgeClass::Approx => {
                    push(&mut self.outgoing[edge.from.index()], index, session, site)?;
                }
                EdgeClass::Param => self.param[edge.from.index()] = true,
                EdgeClass::Create | EdgeClass::Read => {}
            }
        }
        for _ in &graph.derived.hubs {
            admit(session, site, 1, 0)?;
            push(&mut self.spent, false, session, site)?;
        }
        Ok(())
    }

    fn retire<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        // Outer rows own only flat usize buffers; no recursive graph or type
        // payload is copied or retired. Allocator calls remain non-preemptible.
        while !self.outgoing.is_empty() {
            session.retirement_poll(site);
            self.outgoing.pop();
        }
        session.retirement_poll(site);
        drop(self.outgoing);
        session.retirement_poll(site);
        drop(self.param);
        session.retirement_poll(site);
        drop(self.spent);
        session.retirement_poll(site);
        drop(self.queue);
    }
}

impl ExpandedReachGraph {
    fn extend_closure<O: ExecutionObserver>(
        &self,
        scratch: &mut Scratch,
        reached: &mut BTreeMap<ReachNode, Option<ReachEdge>>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<(), ObservedValueError> {
        let mut cursor = 0;
        while cursor < scratch.queue.len() {
            admit(session, site, 1, 0)?;
            let node = scratch.queue[cursor];
            cursor += 1;
            if self.is_seed(node.index()) {
                continue;
            }
            for &index in &scratch.outgoing[node.index()] {
                admit(session, site, 1, 0)?;
                let edge = self.edges[index];
                if insert(reached, edge.to, Some(edge), session, site)? {
                    push(&mut scratch.queue, edge.to, session, site)?;
                }
            }
            let Some(facts) = self.derived.facts_from.get(node.index()) else {
                continue;
            };
            for &fact in facts {
                admit(session, site, 1, 0)?;
                let hub = self.derived.facts[fact as usize].hub as usize;
                if scratch.spent[hub] {
                    continue;
                }
                scratch.spent[hub] = true;
                for &target in &self.derived.hubs[hub].targets {
                    admit(
                        session,
                        site,
                        observed_btree::population_work(reached.len())?,
                        0,
                    )?;
                    if reached.contains_key(&target) {
                        continue;
                    }
                    let Some(edge) = self.logical_edge_observed(node, target, session, site)?
                    else {
                        continue;
                    };
                    insert(reached, target, Some(edge), session, site)?;
                    push(&mut scratch.queue, target, session, site)?;
                }
            }
        }
        Ok(())
    }

    fn logical_edge_observed<O: ExecutionObserver>(
        &self,
        from: ReachNode,
        to: ReachNode,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Option<ReachEdge>, ObservedValueError> {
        admit(session, site, 1, 0)?;
        let Some(holders) = self.derived.hubs_of.get(to.index()) else {
            return Ok(None);
        };
        let Some(facts) = self.derived.facts_from.get(from.index()) else {
            return Ok(None);
        };
        let mut found: Option<ReachEdge> = None;
        for &fact in facts {
            admit(session, site, 1, 0)?;
            let fact = &self.derived.facts[fact as usize];
            if !holds_hub(holders, fact.hub, session, site)? {
                continue;
            }
            match &mut found {
                None => {
                    found = Some(ReachEdge {
                        from,
                        to,
                        class: EdgeClass::Approx,
                        site: fact.site,
                        via_drop: fact.via_drop,
                    })
                }
                Some(edge) if edge.via_drop && !fact.via_drop => {
                    edge.via_drop = false;
                    edge.site = fact.site;
                }
                Some(_) => {}
            }
            if found.is_some_and(|edge| !edge.via_drop) {
                break;
            }
        }
        Ok(found)
    }
}

fn holds_hub<O: ExecutionObserver>(
    holders: &[(u32, u32)],
    hub: u32,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<bool, ObservedValueError> {
    let (mut left, mut right) = (0, holders.len());
    while left < right {
        admit(session, site, 1, 0)?;
        let middle = left + (right - left) / 2;
        match holders[middle].0.cmp(&hub) {
            core::cmp::Ordering::Less => left = middle + 1,
            core::cmp::Ordering::Greater => right = middle,
            core::cmp::Ordering::Equal => return Ok(true),
        }
    }
    Ok(false)
}

fn insert<O: ExecutionObserver>(
    reached: &mut BTreeMap<ReachNode, Option<ReachEdge>>,
    node: ReachNode,
    edge: Option<ReachEdge>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<bool, ObservedValueError> {
    admit(
        session,
        site,
        observed_btree::population_work(reached.len())?,
        0,
    )?;
    if reached.contains_key(&node) {
        return Ok(false);
    }
    let cost = observed_btree::insertion_cost::<ReachNode, Option<ReachEdge>>(reached.len())?;
    admit(session, site, cost.work, cost.copy_bytes)?;
    reached.insert(node, edge);
    Ok(true)
}

fn push<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<(), ObservedValueError> {
    if values.len() == values.capacity() {
        let capacity = values
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let images = capacity
            .checked_add(values.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let bytes = images
            .checked_mul(size_of::<T>())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        // Price the requested new buffer, relocation of existing initialized
        // elements, and their eventual retirement BEFORE requesting growth.
        admit(
            session,
            site,
            images
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            bytes,
        )?;
        values
            .try_reserve_exact(capacity - values.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    admit(session, site, 1, size_of::<T>())?;
    values.push(value);
    Ok(())
}

fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Reachability,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}

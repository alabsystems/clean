// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Default)]
struct Work {
    starts: Vec<usize>,
    fill: Vec<usize>,
    incoming: Vec<u32>,
    distances: [Vec<u32>; 4],
    parents: LevelParents,
    merged: Vec<u32>,
    fired: Vec<bool>,
    queue: Vec<usize>,
    labels: Vec<Verdict>,
    justifications: Vec<Option<Justification>>,
    definitions: Vec<(DefinitionKey, Verdict)>,
    defects: Vec<ReachDefect>,
}

pub(super) fn solve<O: ExecutionObserver>(
    graph: &ExpandedReachGraph,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<(ReachCertificate, LevelParents, Option<ReachFallback>)> {
    admit(session, site, 1, size_of::<Work>())?;
    let mut work = Work::default();
    let result = work.run(graph, session, site);
    work.retire_scratch(session, site);
    let result = result.and_then(|error| {
        admit(session, site, 0, 0)?;
        Ok(error)
    });
    match result {
        Ok(error) => {
            let fallback = if work.defects.is_empty() {
                error.map(ReachFallback::CertificateRejected)
            } else {
                Some(ReachFallback::Defects(core::mem::take(&mut work.defects)))
            };
            Ok((
                ReachCertificate {
                    labels: work.labels,
                    justifications: work.justifications,
                    definitions: work.definitions,
                },
                work.parents,
                fallback,
            ))
        }
        Err(error) => {
            retire_solution(
                ReachCertificate {
                    labels: work.labels,
                    justifications: work.justifications,
                    definitions: work.definitions,
                },
                work.parents,
                session,
                site,
            );
            retire_vec(work.defects, session, site);
            if session.first_refusal().is_some() {
                Err(ObservedValueError::AdmissionRefused)
            } else {
                Err(error)
            }
        }
    }
}

impl Work {
    fn run<O: ExecutionObserver>(
        &mut self,
        graph: &ExpandedReachGraph,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<Option<CertificateError>> {
        let count = graph.nodes.len();
        admit(session, site, 1, 0)?;
        if u32::try_from(count).is_err() {
            return Err(ObservedValueError::CapacityOverflow);
        }
        self.adjacency(graph, session, site)?;
        for level in 0..4 {
            admit(session, site, 1, 0)?;
            filled(count, u32::MAX, &mut self.distances[level], session, site)?;
            filled(count, NO_PARENT, &mut self.parents[level], session, site)?;
        }
        for (level, verdict) in Verdict::LEVELS.iter().enumerate() {
            admit(session, site, 1, 0)?;
            self.level(graph, level, *verdict, session, site)?;
        }
        self.finish(graph, session, site)?;
        for defect in &graph.defects {
            admit(session, site, 1, 0)?;
            push(&mut self.defects, defect.clone(), session, site)?;
        }
        if self.defects.is_empty() {
            check(
                graph,
                &self.labels,
                &self.justifications,
                &self.definitions,
                session,
                site,
            )
            .map(Result::err)
        } else {
            Ok(None)
        }
    }

    fn adjacency<O: ExecutionObserver>(
        &mut self,
        graph: &ExpandedReachGraph,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let count = graph
            .nodes
            .len()
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        filled(count, 0usize, &mut self.starts, session, site)?;
        let edges = &graph.edges[..graph.base_edges];
        for edge in edges {
            admit(session, site, 1, 0)?;
            let slot = &mut self.starts[edge.to.index() + 1];
            *slot = slot
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        for index in 0..graph.nodes.len() {
            admit(session, site, 1, 0)?;
            self.starts[index + 1] = self.starts[index + 1]
                .checked_add(self.starts[index])
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        for value in &self.starts {
            push(&mut self.fill, *value, session, site)?;
        }
        filled(edges.len(), 0u32, &mut self.incoming, session, site)?;
        for (index, edge) in edges.iter().enumerate() {
            admit(session, site, 1, 0)?;
            let slot = &mut self.fill[edge.to.index()];
            self.incoming[*slot] =
                u32::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?;
            *slot += 1;
        }
        Ok(())
    }

    fn level<O: ExecutionObserver>(
        &mut self,
        graph: &ExpandedReachGraph,
        level: usize,
        verdict: Verdict,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        admit(session, site, 1, 0)?;
        self.fired.clear();
        self.queue.clear();
        filled(
            graph.derived.hubs.len(),
            false,
            &mut self.fired,
            session,
            site,
        )?;
        for node in 0..graph.nodes.len() {
            admit(session, site, 1, 0)?;
            if graph.is_seed(node) || (verdict == Verdict::Unknown && graph.is_sink(node)) {
                self.distances[level][node] = 0;
                push(&mut self.queue, node, session, site)?;
            }
        }
        let mut cursor = 0;
        while cursor < self.queue.len() {
            admit(session, site, 1, 0)?;
            let node = self.queue[cursor];
            cursor += 1;
            for &index in &self.incoming[self.starts[node]..self.starts[node + 1]] {
                admit(session, site, 1, 0)?;
                let edge = &graph.edges[index as usize];
                let from = edge.from.index();
                if edge.class.cap() >= verdict && self.distances[level][from] == u32::MAX {
                    self.distances[level][from] = self.distances[level][node]
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    self.parents[level][from] = index;
                    push(&mut self.queue, from, session, site)?;
                }
            }
            if EdgeClass::Approx.cap() < verdict {
                continue;
            }
            self.hubs(graph, node, level, session, site)?;
        }
        Ok(())
    }

    fn hubs<O: ExecutionObserver>(
        &mut self,
        graph: &ExpandedReachGraph,
        node: usize,
        level: usize,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let Some(holders) = graph.derived.hubs_of.get(node) else {
            return Ok(());
        };
        admit(session, site, 1, 0)?;
        self.merged.clear();
        for &(hub, position) in holders {
            admit(session, site, 1, 0)?;
            if self.fired[hub as usize] {
                continue;
            }
            self.fired[hub as usize] = true;
            let hub_node = graph.derived.hub_base + hub as usize;
            self.distances[level][hub_node] = self.distances[level][node];
            self.parents[level][hub_node] = graph.derived.hubs[hub as usize].first_edge + position;
            for &fact in &graph.derived.hubs[hub as usize].facts {
                push(&mut self.merged, fact, session, site)?;
            }
        }
        // The ordinary solver sorts fact IDs. Insertion sort exposes every
        // actual comparison/move to the same observer and keeps that exact order.
        for index in 1..self.merged.len() {
            admit(session, site, 1, 0)?;
            let value = self.merged[index];
            let mut position = index;
            while position > 0 {
                admit(session, site, 1, 0)?;
                if self.merged[position - 1] <= value {
                    break;
                }
                admit(session, site, 1, size_of::<u32>())?;
                self.merged[position] = self.merged[position - 1];
                position -= 1;
            }
            admit(session, site, 1, size_of::<u32>())?;
            self.merged[position] = value;
        }
        for &index in &self.merged {
            admit(session, site, 1, 0)?;
            let fact = &graph.derived.facts[index as usize];
            let from = fact.from.index();
            if self.distances[level][from] == u32::MAX {
                self.distances[level][from] = self.distances[level][node]
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.parents[level][from] = fact.edge;
                push(&mut self.queue, from, session, site)?;
            }
        }
        Ok(())
    }

    fn finish<O: ExecutionObserver>(
        &mut self,
        graph: &ExpandedReachGraph,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        for node in 0..graph.nodes.len() {
            admit(session, site, 1, 0)?;
            let level = (0..4).find(|level| self.distances[*level][node] != u32::MAX);
            let label = level.map_or(Verdict::Quiet, |level| Verdict::LEVELS[level]);
            let justification = level.and_then(|level| {
                (graph.base_label(node) != Some(label)).then(|| Justification {
                    rank: self.distances[level][node]
                        .saturating_mul(2)
                        .saturating_add(u32::from(graph.is_hub_index(node))),
                    edge: self.parents[level][node],
                })
            });
            push(&mut self.labels, label, session, site)?;
            push(&mut self.justifications, justification, session, site)?;
        }
        let mut joined = BTreeMap::new();
        let result = (|| {
            join(graph, &self.labels, &mut joined, session, site)?;
            while !joined.is_empty() {
                tree_lookup(joined.len(), session, site)?;
                let Some(value) = joined.pop_first() else {
                    break;
                };
                push(&mut self.definitions, value, session, site)?;
            }
            Ok(())
        })();
        retire_join(joined, session, site);
        result
    }

    fn retire_scratch<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_vec(core::mem::take(&mut self.starts), session, site);
        retire_vec(core::mem::take(&mut self.fill), session, site);
        retire_vec(core::mem::take(&mut self.incoming), session, site);
        for level in &mut self.distances {
            retire_vec(core::mem::take(level), session, site);
        }
        retire_vec(core::mem::take(&mut self.merged), session, site);
        retire_vec(core::mem::take(&mut self.fired), session, site);
        retire_vec(core::mem::take(&mut self.queue), session, site);
    }
}

pub(super) fn retire_solution<O: ExecutionObserver>(
    certificate: ReachCertificate,
    parents: LevelParents,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    retire_vec(certificate.labels, session, site);
    retire_vec(certificate.justifications, session, site);
    retire_vec(certificate.definitions, session, site);
    for parent in parents {
        retire_vec(parent, session, site);
    }
}

fn join<O: ExecutionObserver>(
    graph: &ExpandedReachGraph,
    labels: &[Verdict],
    joined: &mut BTreeMap<DefinitionKey, Verdict>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<()> {
    for (node, kind) in graph.nodes.iter().enumerate() {
        admit(session, site, 1, 0)?;
        if let ReachNodeKind::Program(ReachNodeSpec {
            definition: Some(key),
            ..
        }) = kind
        {
            tree_cost::<DefinitionKey, Verdict, O>(joined.len(), session, site)?;
            let entry = joined.entry(*key).or_insert(Verdict::Quiet);
            *entry = (*entry).max(labels[node]);
        }
    }
    Ok(())
}

fn retire_join<O: ExecutionObserver>(
    mut joined: BTreeMap<DefinitionKey, Verdict>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !joined.is_empty() {
        session.retirement_poll(site);
        joined.pop_first();
    }
    session.retirement_poll(site);
    drop(joined);
}

pub(super) fn check<O: ExecutionObserver>(
    graph: &ExpandedReachGraph,
    labels: &[Verdict],
    justifications: &[Option<Justification>],
    definitions: &[(DefinitionKey, Verdict)],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<Result<(), CertificateError>> {
    admit(session, site, 1, 0)?;
    if labels.len() != graph.nodes.len() || justifications.len() != graph.nodes.len() {
        return Ok(Err(CertificateError::Shape));
    }
    for (node, (label, justification)) in labels.iter().zip(justifications).enumerate() {
        admit(session, site, 1, 0)?;
        if let Some(base) = graph.base_label(node)
            && (*label != base || justification.is_some())
        {
            return Ok(Err(CertificateError::Base(graph.handle(node))));
        }
    }
    for (index, edge) in graph.edges.iter().enumerate() {
        admit(session, site, 1, 0)?;
        if labels[edge.from.index()] < labels[edge.to.index()].min(edge.class.cap()) {
            return Ok(Err(CertificateError::Unclosed { edge: index }));
        }
    }
    let rank = |index: usize| match justifications[index] {
        Some(reason) => reason.rank,
        None if graph.base_label(index).is_some() => 0,
        None => u32::MAX,
    };
    for node in 0..graph.nodes.len() {
        admit(session, site, 1, 0)?;
        if graph.base_label(node).is_some() {
            continue;
        }
        let justified = match (labels[node], justifications[node]) {
            (Verdict::Quiet, None) => true,
            (Verdict::Quiet, Some(_)) | (_, None) => false,
            (label, Some(reason)) => graph.edges.get(reason.edge as usize).is_some_and(|edge| {
                let target = edge.to.index();
                edge.from.index() == node
                    && edge.class.cap() >= label
                    && (labels[target] > label
                        || (labels[target] == label && rank(target) < reason.rank))
            }),
        };
        if !justified {
            return Ok(Err(CertificateError::Unjustified(graph.handle(node))));
        }
    }
    let mut joined = BTreeMap::new();
    let result = (|| {
        join(graph, labels, &mut joined, session, site)?;
        if joined.len() != definitions.len() {
            return Ok(Err(CertificateError::Definitions));
        }
        for expected in definitions {
            tree_lookup(joined.len(), session, site)?;
            if joined.pop_first().as_ref() != Some(expected) {
                return Ok(Err(CertificateError::Definitions));
            }
        }
        Ok(Ok(()))
    })();
    retire_join(joined, session, site);
    if session.first_refusal().is_some() {
        Err(ObservedValueError::AdmissionRefused)
    } else {
        result
    }
}

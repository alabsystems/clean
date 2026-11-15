// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The uncompressed derivation (trust-ir `5290adb2`'s, edge by edge), kept
//! as the oracle the compressed one is compared with: every derived edge is
//! materialized, and the solver scans them one by one. Test-only. It reads
//! the pools through the same [`ClosedPools`] predicates (laundered data's
//! keyed admission included), so it checks the compression, not them.

use super::*;
use std::collections::btree_map::Entry;

/// Derived APPROX edges by `(from, to)`, as indices into the edge list.
type DerivedEdges = BTreeMap<(ReachNode, ReachNode), usize>;

/// The uncompressed expansion and its solution.
pub(super) struct Reference {
    pub(super) graph: u64,
    pub(super) nodes: Vec<ReachNodeKind>,
    pub(super) edges: Vec<ReachEdge>,
    pub(super) base_edges: usize,
    pub(super) thread_entries: BTreeMap<usize, Option<ReachNode>>,
    pub(super) defects: Vec<ReachDefect>,
    pub(super) pools: ClosedPools,
    pub(super) labels: Vec<Verdict>,
    pub(super) parents: LevelParents,
}

impl Reference {
    pub(super) fn solve(graph: ReachGraph) -> Self {
        let unenumerated = graph
            .nodes
            .iter()
            .any(|kind| matches!(kind, ReachNodeKind::Sink(_)));
        let pools = graph.universe.close(unenumerated);
        let mut reference = Reference {
            graph: graph.id,
            base_edges: graph.edges.len(),
            nodes: graph.nodes,
            edges: graph.edges,
            thread_entries: graph.thread_entries,
            defects: graph.defects,
            pools,
            labels: Vec::new(),
            parents: std::array::from_fn(|_| Vec::new()),
        };
        if reference.defects.is_empty() {
            reference.derive_approx(&graph.universe);
        }
        let (labels, parents) = reference.solve_levels();
        reference.labels = labels;
        reference.parents = parents;
        reference
    }

    fn handle(&self, index: usize) -> ReachNode {
        ReachNode::new(self.graph, index)
    }

    fn node(&self, node: ReachNode) -> Option<&ReachNodeKind> {
        (node.graph == self.graph)
            .then(|| self.nodes.get(node.index()))
            .flatten()
    }

    fn spec(&self, node: ReachNode) -> Option<&ReachNodeSpec> {
        match self.node(node) {
            Some(ReachNodeKind::Program(spec)) => Some(spec),
            _ => None,
        }
    }

    pub(super) fn is_seed(&self, node: usize) -> bool {
        matches!(
            self.nodes[node],
            ReachNodeKind::Program(ReachNodeSpec {
                body: NodeBody::Seed,
                ..
            })
        )
    }

    fn is_sink(&self, node: usize) -> bool {
        matches!(self.nodes[node], ReachNodeKind::Sink(_))
    }

    fn engine_sink(
        &mut self,
        sinks: &mut EngineSinks,
        principal: Option<PrincipalKey>,
    ) -> ReachNode {
        if let Some(sink) = sinks.get(&principal) {
            return *sink;
        }
        let sink = self.handle(self.nodes.len());
        self.nodes.push(ReachNodeKind::Sink(match principal {
            Some(_) => DependencyRefusalKind::OpenPrincipal,
            None => DependencyRefusalKind::UnclosedPool,
        }));
        sinks.insert(principal, sink);
        sink
    }

    /// Derive one APPROX edge. Repeats of `(from, to)` keep one edge, flagged
    /// `via_drop` only if every fact behind it is, so the flag does not
    /// depend on fact order. Returns whether the edge is new.
    fn derive(
        &mut self,
        derived: &mut DerivedEdges,
        from: ReachNode,
        to: ReachNode,
        site: ReachSite,
        via_drop: bool,
    ) -> bool {
        match derived.entry((from, to)) {
            Entry::Vacant(slot) => {
                slot.insert(self.edges.len());
                self.edges.push(ReachEdge {
                    from,
                    to,
                    class: EdgeClass::Approx,
                    site,
                    via_drop,
                });
                true
            }
            Entry::Occupied(slot) => {
                let edge = &mut self.edges[*slot.get()];
                if edge.via_drop && !via_drop {
                    edge.via_drop = false;
                    edge.site = site;
                }
                false
            }
        }
    }

    /// Derive the APPROX edges: every invoke to its visible pool members (and
    /// to an UNKNOWN sink for an open principal, or for unclosed pools), then
    /// rule H to a fixpoint.
    fn derive_approx(&mut self, universe: &IndirectCallUniverse) {
        let mut sinks = EngineSinks::new();
        let mut derived = DerivedEdges::new();
        let unclosed = self.pools.unclosed();
        // (local invoker, external member) pairs: rule H at an indirect call.
        let mut implicit_handoffs: Vec<PoolHandoff> = Vec::new();
        for invoke in &universe.invokes {
            let local = self
                .spec(invoke.node)
                .is_some_and(|spec| spec.locality == Locality::Local);
            let members: Vec<PoolMember> = self.pools.pool(&invoke.key).cloned().collect();
            let mut targets = Vec::new();
            for member in members {
                if local || !member.confined {
                    targets.push(member.member);
                }
                let external = self
                    .spec(member.member)
                    .is_some_and(|spec| spec.locality == Locality::External);
                if local && external && !invoke.carried.is_empty() {
                    implicit_handoffs.push(PoolHandoff {
                        node: invoke.node,
                        callee: member.member,
                        carried: invoke.carried.clone(),
                        site: invoke.site,
                        via_drop: invoke.via_drop,
                    });
                }
            }
            if let Some(principal) = invoke.key.principal()
                && self.pools.open_principals().contains(&principal)
            {
                targets.push(self.engine_sink(&mut sinks, Some(principal)));
            }
            if unclosed {
                targets.push(self.engine_sink(&mut sinks, None));
            }
            for target in targets {
                self.derive(
                    &mut derived,
                    invoke.node,
                    target,
                    invoke.site,
                    invoke.via_drop,
                );
            }
        }

        let handoffs: Vec<&PoolHandoff> = universe
            .handoffs
            .iter()
            .chain(implicit_handoffs.iter())
            .collect();
        if handoffs.is_empty() {
            return;
        }
        let runs_into_seed: BTreeSet<(ReachNode, ReachNode)> = self
            .edges
            .iter()
            .filter(|edge| edge.class == EdgeClass::Run && self.is_seed(edge.to.index()))
            .map(|edge| (edge.from, edge.to))
            .collect();
        let own: Vec<Vec<usize>> = {
            let mut own = vec![Vec::new(); self.nodes.len()];
            for (index, invoke) in universe.invokes.iter().enumerate() {
                own[invoke.node.index()].push(index);
            }
            own
        };
        let everything: Vec<bool> = self
            .nodes
            .iter()
            .map(|kind| match kind {
                ReachNodeKind::Sink(_) => true,
                ReachNodeKind::Program(spec) => spec.body == NodeBody::Opaque,
                ReachNodeKind::Hub => unreachable!("the reference makes no hub"),
            })
            .collect();
        // Each round rebuilds the successor lists and the summaries, so the
        // fixpoint costs O(rounds × (V + E)); a round is needed only when the
        // previous one added an edge. Measured at std scale in P2m.
        loop {
            let mut successors = vec![Vec::new(); self.nodes.len()];
            for edge in &self.edges {
                if matches!(edge.class, EdgeClass::Run | EdgeClass::Approx) {
                    successors[edge.from.index()].push(edge.to.index());
                }
            }
            let mut own = own.clone();
            own.resize(self.nodes.len(), Vec::new());
            let mut everything = everything.clone();
            everything.resize(self.nodes.len(), true);
            let summaries = InvokedKeySummaries::new(&successors, &own, &everything);

            let mut added = false;
            for handoff in &handoffs {
                let mut targets: BTreeSet<ReachNode> = BTreeSet::new();
                let mut open: BTreeSet<PrincipalKey> = BTreeSet::new();
                let mut unenumerated = false;
                if self.is_seed(handoff.callee.index()) {
                    // A hand-off to a thread start: the call that makes it is
                    // a RUN edge, which outranks this one; without that edge
                    // the hand-off is the only fact, and it is charged.
                    if !runs_into_seed.contains(&(handoff.node, handoff.callee)) {
                        targets.insert(handoff.callee);
                    }
                } else {
                    match summaries.of(handoff.callee.index()) {
                        InvokedKeys::Every => {
                            for member in self.pools.members() {
                                if handoff.carried.iter().any(|carried| {
                                    self.pools.admits(carried, &member.key)
                                        && self.pools.may_hold(carried, member)
                                }) {
                                    targets.insert(member.member);
                                }
                            }
                            for principal in self.pools.open_principals() {
                                if handoff
                                    .carried
                                    .iter()
                                    .any(|carried| self.pools.admits_principal(carried, *principal))
                                {
                                    open.insert(*principal);
                                }
                            }
                            unenumerated = unclosed
                                && handoff
                                    .carried
                                    .iter()
                                    .any(|carried| self.pools.may_carry_callable(carried));
                        }
                        // Only while the pools are closed: once they are
                        // not, every invoke reaches the `UnclosedPool` sink,
                        // so a closure holding one invokes `Every` key.
                        InvokedKeys::Some(invoked) => {
                            for index in invoked {
                                let key = &universe.invokes[*index].key;
                                if !handoff
                                    .carried
                                    .iter()
                                    .any(|carried| self.pools.admits(carried, key))
                                {
                                    continue;
                                }
                                targets.extend(
                                    self.pools
                                        .pool(key)
                                        .filter(|member| {
                                            handoff.carried.iter().any(|carried| {
                                                self.pools.admits(carried, key)
                                                    && self.pools.may_hold(carried, member)
                                            })
                                        })
                                        .map(|member| member.member),
                                );
                                if let Some(principal) = key.principal()
                                    && self.pools.open_principals().contains(&principal)
                                {
                                    open.insert(principal);
                                }
                            }
                        }
                    }
                }
                for principal in open {
                    targets.insert(self.engine_sink(&mut sinks, Some(principal)));
                }
                if unenumerated {
                    targets.insert(self.engine_sink(&mut sinks, None));
                }
                for target in targets {
                    added |= self.derive(
                        &mut derived,
                        handoff.node,
                        target,
                        handoff.site,
                        handoff.via_drop,
                    );
                }
            }
            if !added {
                return;
            }
        }
    }

    /// The four backward breadth-first reachabilities, and the labelling and
    /// certificate they give.
    fn solve_levels(&self) -> (Vec<Verdict>, LevelParents) {
        let count = self.nodes.len();
        // Incoming edges, grouped by target (CSR).
        let mut starts = vec![0usize; count + 1];
        for edge in &self.edges {
            starts[edge.to.index() + 1] += 1;
        }
        for index in 0..count {
            starts[index + 1] += starts[index];
        }
        let mut fill = starts.clone();
        let mut incoming = vec![0u32; self.edges.len()];
        for (index, edge) in self.edges.iter().enumerate() {
            let slot = &mut fill[edge.to.index()];
            incoming[*slot] = u32::try_from(index).unwrap_or(u32::MAX);
            *slot += 1;
        }

        let mut distances: [Vec<u32>; 4] = std::array::from_fn(|_| vec![u32::MAX; count]);
        let mut parents: LevelParents = std::array::from_fn(|_| vec![NO_PARENT; count]);
        for (level_index, level) in Verdict::LEVELS.iter().enumerate() {
            let distance = &mut distances[level_index];
            let parent = &mut parents[level_index];
            let mut queue = VecDeque::new();
            for (node, slot) in distance.iter_mut().enumerate() {
                if self.is_seed(node) || (*level == Verdict::Unknown && self.is_sink(node)) {
                    *slot = 0;
                    queue.push_back(node);
                }
            }
            while let Some(node) = queue.pop_front() {
                for &edge_index in &incoming[starts[node]..starts[node + 1]] {
                    let edge = &self.edges[edge_index as usize];
                    let from = edge.from.index();
                    if edge.class.cap() >= *level && distance[from] == u32::MAX {
                        distance[from] = distance[node] + 1;
                        parent[from] = edge_index;
                        queue.push_back(from);
                    }
                }
            }
        }

        let mut labels = vec![Verdict::Quiet; count];
        for (node, label) in labels.iter_mut().enumerate() {
            if let Some(level_index) = (0..4).find(|level| distances[*level][node] != u32::MAX) {
                *label = Verdict::LEVELS[level_index];
            }
        }
        (labels, parents)
    }

    /// The per-definition join: the strongest label among a definition's nodes.
    pub(super) fn join_definitions(&self, labels: &[Verdict]) -> Vec<(DefinitionKey, Verdict)> {
        let mut joined: BTreeMap<DefinitionKey, Verdict> = BTreeMap::new();
        for (node, kind) in self.nodes.iter().enumerate() {
            if let ReachNodeKind::Program(ReachNodeSpec {
                definition: Some(definition),
                ..
            }) = kind
            {
                let entry = joined.entry(*definition).or_insert(Verdict::Quiet);
                *entry = (*entry).max(labels[node]);
            }
        }
        joined.into_iter().collect()
    }

    pub(super) fn verdict(&self, node: ReachNode) -> Verdict {
        self.labels[node.index()]
    }

    pub(super) fn witness(&self, node: ReachNode) -> Option<ReachWitness> {
        let start = node.index();
        let verdict = self.verdict(node);
        if verdict == Verdict::Quiet {
            return None;
        }
        let level = Verdict::LEVELS.iter().position(|level| *level == verdict)?;
        let mut path = Vec::new();
        let mut current = start;
        while self.parents[level][current] != NO_PARENT {
            let edge = self.edges[self.parents[level][current] as usize];
            path.push(edge);
            current = edge.to.index();
        }
        let via_drop = path.iter().any(|edge| edge.via_drop);
        Some(ReachWitness {
            verdict,
            path,
            via_drop,
        })
    }

    pub(super) fn spawn_sites(&self) -> Vec<SpawnSite> {
        self.edges
            .iter()
            .enumerate()
            .filter(|(_, edge)| {
                matches!(edge.class, EdgeClass::Run | EdgeClass::Approx)
                    && self.is_seed(edge.to.index())
            })
            .map(|(index, edge)| SpawnSite {
                edge: *edge,
                entry: self.thread_entries.get(&index).copied().flatten(),
            })
            .collect()
    }

    pub(super) fn thread_closure(
        &self,
        entry: ReachNode,
    ) -> (BTreeMap<ReachNode, Option<ReachEdge>>, bool) {
        let mut reached: BTreeMap<ReachNode, Option<ReachEdge>> = BTreeMap::new();
        let start = entry;
        let count = self.nodes.len();
        let mut outgoing: Vec<Vec<usize>> = vec![Vec::new(); count];
        let mut param = vec![false; count];
        for (index, edge) in self.edges.iter().enumerate() {
            match edge.class {
                EdgeClass::Run | EdgeClass::Approx => outgoing[edge.from.index()].push(index),
                EdgeClass::Param => param[edge.from.index()] = true,
                EdgeClass::Create | EdgeClass::Read => {}
            }
        }
        reached.insert(start, None);
        let mut queue = VecDeque::from([start]);
        while let Some(node) = queue.pop_front() {
            if self.is_seed(node.index()) {
                continue;
            }
            for &index in &outgoing[node.index()] {
                let edge = self.edges[index];
                if let Entry::Vacant(slot) = reached.entry(edge.to) {
                    slot.insert(Some(edge));
                    queue.push_back(edge.to);
                }
            }
        }
        let modelable = reached.keys().all(|node| {
            let index = node.index();
            !param[index]
                && !matches!(self.verdict(*node), Verdict::Unknown | Verdict::Indirect)
                && matches!(
                    self.nodes[index],
                    ReachNodeKind::Program(ReachNodeSpec {
                        body: NodeBody::Walked | NodeBody::Seed | NodeBody::Primitive,
                        ..
                    })
                )
        });
        (reached, modelable)
    }
}

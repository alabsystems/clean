// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier 2 — the lineage equivalence graph (strong evidence, not proof).
//!
//! An **accumulating** graph whose nodes are fact identities (Tier-1 / 1.5 digests) and
//! whose edges are graded *identity hints*, each carrying provenance + a trust level.
//! Two complementary queries:
//!
//! * **`same_class`** — union-find over **all** edges. This clusters likely-equivalent
//!   facts so uniqueness/search only looks *within* a class — the search-space collapse.
//!   Membership is a *candidate* relation, not a proof.
//! * **`soundly_equivalent`** — a path over **sound** edges only ([`Trust::Sound`]:
//!   `defeq` and kernel-checked `proved-iff`). This is the relation you may trust for
//!   dedup: it never crosses a `conjectured` / `rewrite-canonical` / `import-alias` link.
//!
//! The graph **converges**: replacing a `conjectured` edge with a later `proved-iff`
//! upgrades the pair from candidate to soundly-equivalent, moving the corpus toward the
//! undecidable logical-equivalence tier **without ever claiming it**.

use std::collections::{HashMap, VecDeque};

use serde::{Deserialize, Serialize};

/// How much an edge may be trusted, worst → best.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Trust {
    /// Agent/heuristic-asserted — never auto-trusted.
    Conjectured,
    /// Cross-system same-name provenance — evidence, not a proof.
    Provenance,
    /// Deterministic syntactic canonicalisation (Tier 1.5) — strong, but not a proof.
    Deterministic,
    /// Kernel-decidable / kernel-checked — sound.
    Sound,
}

/// The kind of identity hint an edge records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EdgeKind {
    /// Definitionally equal (Tier 1) — sound.
    Defeq,
    /// Same Tier-1.5 rewrite-canonical digest — deterministic, not a proof.
    RewriteCanonical,
    /// A kernel-checked `A ↔ B` certificate — the only *sound* logical-equivalence link.
    ProvedIff,
    /// Cross-system same-name import provenance.
    ImportAlias,
    /// Conjectured / agent-asserted.
    Conjectured,
}

impl EdgeKind {
    /// The trust level of this hint.
    #[must_use]
    pub(crate) fn trust(self) -> Trust {
        match self {
            EdgeKind::Defeq | EdgeKind::ProvedIff => Trust::Sound,
            EdgeKind::RewriteCanonical => Trust::Deterministic,
            EdgeKind::ImportAlias => Trust::Provenance,
            EdgeKind::Conjectured => Trust::Conjectured,
        }
    }

    /// May this edge be trusted for sound dedup?
    #[must_use]
    pub(crate) fn is_sound(self) -> bool {
        self.trust() == Trust::Sound
    }
}

/// A graded identity hint between two fact identities.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Edge {
    /// Endpoint fact identity (digest).
    pub from: String,
    /// Endpoint fact identity (digest).
    pub to: String,
    /// The hint kind (carries trust).
    pub kind: EdgeKind,
    /// Free-form justification — a certificate id, the matching digest, the source system, …
    pub evidence: String,
}

/// One node of the lineage graph.
#[derive(Debug)]
struct Node {
    /// union-find parent (over ALL edges — clustering / search).
    parent: usize,
    /// union-find rank.
    rank: usize,
    /// incident edges, as indices into `LineageGraph::edges`.
    adj: Vec<usize>,
}

/// The accumulating lineage equivalence graph.
#[derive(Debug, Default)]
pub struct LineageGraph {
    /// digest → dense node index.
    index: HashMap<String, usize>,
    /// One slot per node, keyed by the dense index `index` hands out. Its
    /// length is the node count; the union-find parent, rank and adjacency of
    /// a node live in ONE slot, so they cannot drift apart in length. No
    /// separate index→digest `Vec<String>` is kept — that would be a dead,
    /// write-only allocation per node on the corpus-scale lineage build.
    nodes: Vec<Node>,
    /// all edges, in insertion order (the audit log).
    edges: Vec<Edge>,
}

impl LineageGraph {
    /// A fresh, empty graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn node(&mut self, digest: &str) -> usize {
        if let Some(&i) = self.index.get(digest) {
            return i;
        }
        let i = self.nodes.len();
        self.index.insert(digest.to_string(), i);
        self.nodes.push(Node {
            parent: i,
            rank: 0,
            adj: Vec::new(),
        });
        i
    }

    fn parent_of(&self, x: usize) -> Option<usize> {
        self.nodes.get(x).map(|n| n.parent)
    }

    fn set_parent(&mut self, x: usize, parent: usize) {
        if let Some(n) = self.nodes.get_mut(x) {
            n.parent = parent;
        }
    }

    /// The class root of node `x`. Every index this graph handles came from
    /// `node`, and every parent link points at a node, so each lookup below
    /// finds its slot; an index with no slot is answered as its own root
    /// instead of indexed out of bounds.
    fn find(&mut self, mut x: usize) -> usize {
        while let Some(p) = self.parent_of(x) {
            if p == x {
                break;
            }
            let grand = self.parent_of(p).unwrap_or(p);
            self.set_parent(x, grand); // path halving
            x = grand;
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (Some(rank_a), Some(rank_b)) = (
            self.nodes.get(ra).map(|n| n.rank),
            self.nodes.get(rb).map(|n| n.rank),
        ) else {
            return;
        };
        match rank_a.cmp(&rank_b) {
            std::cmp::Ordering::Less => self.set_parent(ra, rb),
            std::cmp::Ordering::Greater => self.set_parent(rb, ra),
            std::cmp::Ordering::Equal => {
                self.set_parent(rb, ra);
                if let Some(n) = self.nodes.get_mut(ra) {
                    // Union-by-rank keeps a rank below log2(node count);
                    // saturating states that bound's consequence without a
                    // panicking add.
                    n.rank = rank_a.saturating_add(1);
                }
            }
        }
    }

    /// Record an identity hint. Idempotent on the union; the edge is always logged so the
    /// "why are these the same?" question always has an answer.
    pub fn add_edge(&mut self, from: &str, to: &str, kind: EdgeKind, evidence: impl Into<String>) {
        let (fi, ti) = (self.node(from), self.node(to));
        let edge_idx = self.edges.len();
        self.edges.push(Edge {
            from: from.to_string(),
            to: to.to_string(),
            kind,
            evidence: evidence.into(),
        });
        for i in [fi, ti] {
            if let Some(n) = self.nodes.get_mut(i) {
                n.adj.push(edge_idx);
            }
        }
        self.union(fi, ti);
    }

    /// Are `a` and `b` in the same equivalence *class* (connected by edges of any trust)?
    /// A candidate relation — narrows the search space; not a soundness claim.
    #[must_use]
    pub fn same_class(&mut self, a: &str, b: &str) -> bool {
        match (self.index.get(a).copied(), self.index.get(b).copied()) {
            (Some(ai), Some(bi)) => self.find(ai) == self.find(bi),
            _ => false,
        }
    }

    /// Are `a` and `b` connected by a path of **sound** edges only (`defeq` / `proved-iff`)?
    /// The relation safe to trust for dedup. Reflexive on a known node.
    #[must_use]
    pub fn soundly_equivalent(&self, a: &str, b: &str) -> bool {
        let (Some(&ai), Some(&bi)) = (self.index.get(a), self.index.get(b)) else {
            return false;
        };
        if ai == bi {
            return true;
        }
        // A set grown per visited node, not a `vec![false; node_count]` sized up
        // front: the search usually stops long before it has seen every node,
        // and the bulk allocation had no bound the verifier could check.
        let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
        let mut q = VecDeque::new();
        seen.insert(ai);
        q.push_back(ai);
        while let Some(n) = q.pop_front() {
            let incident = self
                .nodes
                .get(n)
                .map_or(&[] as &[usize], |node| node.adj.as_slice());
            for e in incident.iter().filter_map(|&ei| self.edges.get(ei)) {
                if !e.kind.is_sound() {
                    continue;
                }
                let other = if self.index[&e.from] == n {
                    self.index[&e.to]
                } else {
                    self.index[&e.from]
                };
                if other == bi {
                    return true;
                }
                if seen.insert(other) {
                    q.push_back(other);
                }
            }
        }
        false
    }

    /// All edges incident to `digest` — the justification log for its memberships.
    // Query API awaiting a production caller; kept alive by its membership test.
    #[cfg_attr(not(test), expect(dead_code))]
    #[must_use]
    pub(crate) fn edges_of(&self, digest: &str) -> Vec<&Edge> {
        let incident = self
            .index
            .get(digest)
            .and_then(|&i| self.nodes.get(i))
            .map_or(&[] as &[usize], |node| node.adj.as_slice());
        incident
            .iter()
            .filter_map(|&ei| self.edges.get(ei))
            .collect()
    }

    /// The full edge log in insertion order — the serializable audit trail (each [`Edge`]
    /// is `Serialize`), so a built graph can be persisted and re-loaded.
    #[must_use]
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }

    /// The number of distinct equivalence *classes* (connected components over all edges).
    /// A multi-member class is a set of fact identities the graph believes are the same
    /// object; this count is the "how much did lineage collapse the corpus?" headline.
    #[must_use]
    pub fn class_count(&mut self) -> usize {
        let n = self.nodes.len();
        let mut roots: std::collections::HashSet<usize> = std::collections::HashSet::new();
        for i in 0..n {
            let r = self.find(i);
            roots.insert(r);
        }
        roots.len()
    }

    /// Number of nodes / edges (for stats).
    #[must_use]
    pub fn len(&self) -> (usize, usize) {
        (self.nodes.len(), self.edges.len())
    }

    /// Is the graph empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression (Trust verified lane, 2026-10-03): `find` indexed
    /// `parent[x]` unchecked, and the stage1 verifier's counterexample was
    /// `x = 0` on an empty graph. An index with no node is now its own root,
    /// and union-find over real nodes (path halving, union by rank, a long
    /// chain) still answers as before.
    #[test]
    fn test_find_without_a_node_is_its_own_root() {
        let mut g = LineageGraph::new();
        assert_eq!(g.find(0), 0);
        g.add_edge("a", "b", EdgeKind::Conjectured, "x");
        assert_eq!(g.find(7), 7);
        assert_eq!(g.len(), (2, 1));

        let mut chain = LineageGraph::new();
        let names: Vec<String> = (0..64).map(|i| format!("n{i}")).collect();
        for w in names.windows(2) {
            chain.add_edge(&w[0], &w[1], EdgeKind::Defeq, "chain");
        }
        assert_eq!(chain.class_count(), 1);
        assert!(chain.same_class("n0", "n63"));
        assert!(chain.soundly_equivalent("n0", "n63"));
        assert_eq!(chain.edges_of("n5").len(), 2);
        assert!(chain.edges_of("absent").is_empty());
    }

    #[test]
    fn test_trust_ordering() {
        assert!(Trust::Conjectured < Trust::Provenance);
        assert!(Trust::Provenance < Trust::Deterministic);
        assert!(Trust::Deterministic < Trust::Sound);
        assert!(EdgeKind::Defeq.is_sound() && EdgeKind::ProvedIff.is_sound());
        assert!(!EdgeKind::RewriteCanonical.is_sound());
        assert!(!EdgeKind::Conjectured.is_sound());
    }

    #[test]
    fn test_clustering_vs_sound_equivalence() {
        let mut g = LineageGraph::new();
        // a ≡ b by defeq (sound); b ~ c by conjecture (clusters, not sound).
        g.add_edge("a", "b", EdgeKind::Defeq, "is_def_eq");
        g.add_edge("b", "c", EdgeKind::Conjectured, "agent guess");

        // Clustering: a, b, c all in one class (search space collapses).
        assert!(g.same_class("a", "c"));
        // Sound: a≡b yes; a≡c NO (the b—c link is conjectured).
        assert!(g.soundly_equivalent("a", "b"));
        assert!(!g.soundly_equivalent("a", "c"));
        // unknown node → not equivalent / not in class.
        assert!(!g.same_class("a", "z"));
        assert!(!g.soundly_equivalent("a", "z"));
    }

    #[test]
    fn test_proved_iff_upgrades_to_sound() {
        let mut g = LineageGraph::new();
        g.add_edge("a", "b", EdgeKind::Defeq, "is_def_eq");
        g.add_edge("b", "c", EdgeKind::Conjectured, "guess");
        assert!(!g.soundly_equivalent("a", "c"));
        // A later kernel-checked A↔B certificate upgrades b—c to sound …
        g.add_edge("b", "c", EdgeKind::ProvedIff, "cert:blake3:dead…beef");
        // … so now a — b — c is a fully sound path.
        assert!(g.soundly_equivalent("a", "c"));
    }

    #[test]
    fn test_edges_of_justifies_membership() {
        let mut g = LineageGraph::new();
        g.add_edge("x", "y", EdgeKind::RewriteCanonical, "same tier-1.5 digest");
        let just = g.edges_of("x");
        assert_eq!(just.len(), 1);
        assert_eq!(just[0].kind, EdgeKind::RewriteCanonical);
        assert_eq!(just[0].evidence, "same tier-1.5 digest");
    }

    #[test]
    fn test_edges_log_and_class_count() {
        let mut g = LineageGraph::new();
        // Class {a,b,c} via two edges; isolated node d (added by a self-less edge to itself
        // is not allowed, so add d via an edge d—d-less path: use a separate class {d,e}).
        g.add_edge("a", "b", EdgeKind::RewriteCanonical, "sem:1");
        g.add_edge("b", "c", EdgeKind::Defeq, "is_def_eq");
        g.add_edge("d", "e", EdgeKind::RewriteCanonical, "sem:2");
        // 5 nodes, 3 edges, 2 classes ({a,b,c}, {d,e}).
        assert_eq!(g.len(), (5, 3));
        assert_eq!(g.edges().len(), 3);
        assert_eq!(g.class_count(), 2);
        // The edge log is the full serializable audit trail in insertion order.
        assert_eq!(g.edges()[0].evidence, "sem:1");
        assert_eq!(g.edges()[2].kind, EdgeKind::RewriteCanonical);
    }

    /// Regression (Trust verified lane, 2026-10-02): equal-rank `union` did
    /// `rank += 1`, a panicking add. It saturates now, and the union is still
    /// recorded.
    #[test]
    fn test_union_at_max_rank_saturates_and_still_unions() {
        let mut g = LineageGraph::new();
        let (a, b) = (g.node("a"), g.node("b"));
        g.nodes[a].rank = usize::MAX;
        g.nodes[b].rank = usize::MAX;
        g.union(a, b);
        let root = g.find(a);
        assert_eq!(root, g.find(b));
        assert_eq!(g.nodes[root].rank, usize::MAX);
    }

    /// The `seen` set replaced a node-count-sized bit vector; a sound path that
    /// needs several hops through a branching graph is still found, and a node
    /// reached only through an unsound edge still is not.
    #[test]
    fn test_soundly_equivalent_multi_hop_with_set_frontier() {
        let mut g = LineageGraph::new();
        g.add_edge("a", "b", EdgeKind::Defeq, "1");
        g.add_edge("a", "x", EdgeKind::Defeq, "2");
        g.add_edge("x", "a", EdgeKind::Defeq, "3");
        g.add_edge("b", "c", EdgeKind::Defeq, "4");
        g.add_edge("c", "d", EdgeKind::Conjectured, "5");
        assert!(g.soundly_equivalent("a", "c"));
        assert!(g.soundly_equivalent("c", "x"));
        assert!(!g.soundly_equivalent("a", "d"));
    }
}

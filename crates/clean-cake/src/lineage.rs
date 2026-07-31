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

/// The accumulating lineage equivalence graph.
#[derive(Debug, Default)]
pub struct LineageGraph {
    /// digest → dense node index.
    index: HashMap<String, usize>,
    /// union-find parent (over ALL edges — clustering / search). Its length is
    /// the node count (`index`, `parent`, `rank`, `adj` grow together in `node`),
    /// so no separate index→digest `Vec<String>` is kept — that would be a dead,
    /// write-only allocation per node on the corpus-scale lineage build.
    parent: Vec<usize>,
    /// union-find rank.
    rank: Vec<usize>,
    /// adjacency keyed by node index, edge index into `edges`.
    adj: Vec<Vec<usize>>,
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
        let i = self.parent.len();
        self.index.insert(digest.to_string(), i);
        self.parent.push(i);
        self.rank.push(0);
        self.adj.push(Vec::new());
        i
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]]; // path halving
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra;
        } else {
            self.parent[rb] = ra;
            self.rank[ra] += 1;
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
        self.adj[fi].push(edge_idx);
        self.adj[ti].push(edge_idx);
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
        let mut seen = vec![false; self.parent.len()];
        let mut q = VecDeque::new();
        seen[ai] = true;
        q.push_back(ai);
        while let Some(n) = q.pop_front() {
            for &ei in &self.adj[n] {
                let e = &self.edges[ei];
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
                if !seen[other] {
                    seen[other] = true;
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
        match self.index.get(digest) {
            Some(&i) => self.adj[i].iter().map(|&ei| &self.edges[ei]).collect(),
            None => Vec::new(),
        }
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
        let n = self.parent.len();
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
        (self.parent.len(), self.edges.len())
    }

    /// Is the graph empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}

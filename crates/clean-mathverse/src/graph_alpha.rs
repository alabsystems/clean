// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathematical knowledge graph: concepts, edges, and conjecture queue.
//!
//! The knowledge graph is an **index structure**, not a reasoning engine.
//! It stores relationships between mathematical objects.

use std::collections::{BTreeMap, VecDeque};

use serde::{Deserialize, Serialize};

use crate::equivalence::EquivalenceDetector;
use crate::error::MathverseResult;
use crate::search::{EdgeFilter, SubGraph};
use crate::types::{
    ConceptIdx, ConjectureIdx, ConstantIdx, ExprIdx, MathverseConstantHeader, SourceSystem,
};

use clean_kernel::flat::{FlatExpr, FlatTag};

/// A node in the mathematical knowledge graph.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConceptNode {
    Theorem {
        constant_idx: ConstantIdx,
    },
    Structure {
        name: String,
        axioms: Vec<ConstantIdx>,
    },
    ComplexityClass {
        name: String,
        definition: ConstantIdx,
        containments: Vec<ConstantIdx>,
    },
    NNArchPattern {
        architecture: ArchSpec,
        certs: Vec<ConstantIdx>,
    },
    Conjecture {
        statement_idx: ExprIdx,
        source: ConjectureSource,
        status: ConjectureStatus,
    },
}

/// Neural network architecture specification for pattern-based retrieval.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArchSpec {
    pub layer_types: Vec<String>,
    pub input_dim: Vec<u32>,
    pub output_dim: Vec<u32>,
}

/// How a conjecture was produced.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConjectureSource {
    AutoFormalized {
        source_doc: String,
    },
    Enumerated {
        depth: u8,
    },
    Analogy {
        from: ConstantIdx,
        via_edge: ConceptIdx,
    },
    ProofTransfer {
        source_system: SourceSystem,
    },
    UserSubmitted,
}

/// Current status of a conjecture.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConjectureStatus {
    Pending,
    Attempting { attempts: u64 },
    Proven { proof: ConstantIdx },
    Disproven { counterexample_desc: String },
    Timeout,
}

/// An edge in the knowledge graph.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConceptEdge {
    Generalizes,
    SpecialCase,
    Analogous { strength: f32 },
    Equivalent { proof: Option<ConstantIdx> },
    DependsOn,
    InstanceOf,
    ReducesTo,
    Separates,
    CertifiesProperty,
}

/// Confidence level for cross-system equivalences.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum EquivConfidence {
    Exact,
    ProvedEquivalent,
    ErasedCandidate { score: f32 },
    ManualReview,
}

/// Priority-ordered queue of conjectures for consumer systems.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ConjectureQueue {
    queue: BTreeMap<u32, Vec<ConjectureIdx>>,
}

impl ConjectureQueue {
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a conjecture at the given priority (lower = higher priority).
    pub fn push(&mut self, priority: u32, idx: ConjectureIdx) {
        self.queue.entry(priority).or_default().push(idx);
    }

    /// Pop the highest-priority conjecture.
    pub fn pop(&mut self) -> Option<(u32, ConjectureIdx)> {
        let first_key = *self.queue.keys().next()?;
        let vec = self.queue.get_mut(&first_key)?;
        let idx = vec.pop()?;
        if vec.is_empty() {
            self.queue.remove(&first_key);
        }
        Some((first_key, idx))
    }

    pub fn len(&self) -> usize {
        self.queue.values().map(Vec::len).sum()
    }
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }
}

/// Adjacency-list knowledge graph over [`ConceptNode`] / [`ConceptEdge`].
///
/// Nodes are indexed by `ConceptIdx` (u32). Edges are stored in a flat
/// vec with forward and reverse adjacency lists for O(1) neighbor access.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ConceptGraph {
    nodes: Vec<ConceptNode>,
    edges: Vec<(ConceptIdx, ConceptIdx, ConceptEdge)>,
    adjacency: Vec<Vec<usize>>,
    reverse_adjacency: Vec<Vec<usize>>,
    name_to_node: hashbrown::HashMap<String, ConceptIdx>,
    constant_to_node: hashbrown::HashMap<ConstantIdx, ConceptIdx>,
}

impl ConceptGraph {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a node, returning its index.
    pub fn add_node(&mut self, node: ConceptNode) -> ConceptIdx {
        let idx = self.nodes.len() as ConceptIdx;
        self.nodes.push(node);
        self.adjacency.push(Vec::new());
        self.reverse_adjacency.push(Vec::new());
        idx
    }

    /// Add a node with a name registration for lookup.
    pub fn add_named_node(&mut self, name: &str, node: ConceptNode) -> ConceptIdx {
        let idx = self.add_node(node);
        self.name_to_node.insert(name.to_owned(), idx);
        idx
    }

    /// Add a directed edge, updating forward and reverse adjacency lists.
    pub fn add_edge(&mut self, from: ConceptIdx, to: ConceptIdx, edge: ConceptEdge) {
        let edge_idx = self.edges.len();
        self.edges.push((from, to, edge));
        if let Some(adj) = self.adjacency.get_mut(from as usize) {
            adj.push(edge_idx);
        }
        if let Some(radj) = self.reverse_adjacency.get_mut(to as usize) {
            radj.push(edge_idx);
        }
    }

    pub fn node(&self, idx: ConceptIdx) -> Option<&ConceptNode> {
        self.nodes.get(idx as usize)
    }
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn lookup_name(&self, name: &str) -> Option<ConceptIdx> {
        self.name_to_node.get(name).copied()
    }

    pub fn lookup_constant(&self, idx: ConstantIdx) -> Option<ConceptIdx> {
        self.constant_to_node.get(&idx).copied()
    }

    /// Register a mapping from a constant index to a graph node.
    pub fn register_constant(&mut self, constant_idx: ConstantIdx, node_idx: ConceptIdx) {
        self.constant_to_node.insert(constant_idx, node_idx);
    }

    /// Outgoing edge indices for a node.
    pub fn neighbors(&self, idx: ConceptIdx) -> &[usize] {
        self.adjacency
            .get(idx as usize)
            .map_or(&[], |v| v.as_slice())
    }

    /// Incoming edge indices for a node.
    pub fn reverse_neighbors(&self, idx: ConceptIdx) -> &[usize] {
        self.reverse_adjacency
            .get(idx as usize)
            .map_or(&[], |v| v.as_slice())
    }

    pub fn get_edge(&self, edge_idx: usize) -> Option<&(ConceptIdx, ConceptIdx, ConceptEdge)> {
        self.edges.get(edge_idx)
    }

    /// BFS from `start`, respecting the edge filter. Returns a [`SubGraph`]
    /// with discovered nodes and edges re-indexed to local positions.
    pub fn bfs(&self, start: ConceptIdx, filter: &EdgeFilter) -> SubGraph {
        let max_depth = filter.max_depth.unwrap_or(u32::MAX);
        let mut visited = hashbrown::HashSet::new();
        let mut queue: VecDeque<(ConceptIdx, u32)> = VecDeque::new();
        let mut local_idx = hashbrown::HashMap::<ConceptIdx, usize>::new();
        let mut sub = SubGraph::default();

        if self.node(start).is_none() {
            return sub;
        }

        visited.insert(start);
        queue.push_back((start, 0));
        local_idx.insert(start, 0);
        sub.nodes.push(self.nodes[start as usize].clone());

        while let Some((current, depth)) = queue.pop_front() {
            if depth >= max_depth {
                continue;
            }
            for &ei in self.neighbors(current) {
                let (from, to, ref edge) = self.edges[ei];
                if !Self::edge_passes_filter(edge, filter) {
                    continue;
                }
                let fl = *local_idx.entry(from).or_insert_with(|| {
                    let i = sub.nodes.len();
                    sub.nodes.push(self.nodes[from as usize].clone());
                    i
                });
                let tl = *local_idx.entry(to).or_insert_with(|| {
                    let i = sub.nodes.len();
                    sub.nodes.push(self.nodes[to as usize].clone());
                    i
                });
                sub.edges.push((fl, tl, edge.clone()));
                if visited.insert(to) {
                    queue.push_back((to, depth + 1));
                }
            }
        }
        sub
    }

    /// Shortest path (by hop count) from `from` to `to`, inclusive.
    pub fn find_path(&self, from: ConceptIdx, to: ConceptIdx) -> Option<Vec<ConceptIdx>> {
        if from == to {
            return Some(vec![from]);
        }
        if self.node(from).is_none() || self.node(to).is_none() {
            return None;
        }

        let mut visited = hashbrown::HashSet::new();
        let mut parent: hashbrown::HashMap<ConceptIdx, ConceptIdx> = hashbrown::HashMap::new();
        let mut queue: VecDeque<ConceptIdx> = VecDeque::new();
        visited.insert(from);
        queue.push_back(from);

        while let Some(cur) = queue.pop_front() {
            for &ei in self.neighbors(cur) {
                let (_, nb, _) = self.edges[ei];
                if visited.insert(nb) {
                    parent.insert(nb, cur);
                    if nb == to {
                        let mut path = vec![to];
                        let mut c = to;
                        while c != from {
                            c = parent[&c];
                            path.push(c);
                        }
                        path.reverse();
                        return Some(path);
                    }
                    queue.push_back(nb);
                }
            }
        }
        None
    }

    /// All nodes reachable via `DependsOn` edges (transitive closure).
    pub fn transitive_deps(&self, start: ConceptIdx) -> Vec<ConceptIdx> {
        let mut visited = hashbrown::HashSet::new();
        let mut stack = vec![start];
        let mut result = Vec::new();
        while let Some(cur) = stack.pop() {
            if !visited.insert(cur) {
                continue;
            }
            if cur != start {
                result.push(cur);
            }
            for &ei in self.neighbors(cur) {
                let (_, to, ref edge) = self.edges[ei];
                if matches!(edge, ConceptEdge::DependsOn) {
                    stack.push(to);
                }
            }
        }
        result
    }

    /// Find all nodes connected via `Equivalent` edges (both directions).
    pub fn find_equivalents(&self, node_idx: ConceptIdx) -> Vec<(EquivConfidence, ConceptIdx)> {
        let confidence = |proof: &Option<ConstantIdx>| {
            if proof.is_some() {
                EquivConfidence::ProvedEquivalent
            } else {
                EquivConfidence::ManualReview
            }
        };
        let mut result = Vec::new();
        for &ei in self.neighbors(node_idx) {
            let (_, to, ref edge) = self.edges[ei];
            if let ConceptEdge::Equivalent { ref proof } = edge {
                result.push((confidence(proof), to));
            }
        }
        for &ei in self.reverse_neighbors(node_idx) {
            let (from, _, ref edge) = self.edges[ei];
            if let ConceptEdge::Equivalent { ref proof } = edge {
                result.push((confidence(proof), from));
            }
        }
        result
    }

    /// Serialize the graph to JSON.
    pub fn to_json(&self) -> MathverseResult<String> {
        Ok(serde_json::to_string(self)?)
    }

    /// Deserialize a graph from JSON.
    pub fn from_json(json: &str) -> MathverseResult<Self> {
        Ok(serde_json::from_str(json)?)
    }

    fn edge_passes_filter(edge: &ConceptEdge, filter: &EdgeFilter) -> bool {
        match filter.allowed_edges {
            Some(ref allowed) => allowed.iter().any(|kind| kind.matches(edge)),
            None => true,
        }
    }

    /// Extract a subgraph of all nodes within `radius` hops of `center`.
    ///
    /// Traverses both forward and reverse edges so the neighborhood captures
    /// upstream dependents as well as downstream dependencies. The returned
    /// `SubGraph` re-indexes nodes to local positions.
    pub fn subgraph_around(&self, center: usize, radius: usize) -> SubGraph {
        if center >= self.nodes.len() {
            return SubGraph::default();
        }
        let mut visited = hashbrown::HashSet::new();
        let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
        let mut local_idx = hashbrown::HashMap::<usize, usize>::new();
        let mut sub = SubGraph::default();

        visited.insert(center);
        queue.push_back((center, 0));
        local_idx.insert(center, 0);
        sub.nodes.push(self.nodes[center].clone());

        while let Some((current, depth)) = queue.pop_front() {
            if depth >= radius {
                continue;
            }
            // Forward edges.
            for &ei in self.neighbors(current as ConceptIdx) {
                let (_, to, _) = self.edges[ei];
                let to_us = to as usize;
                if visited.insert(to_us) {
                    let li = sub.nodes.len();
                    sub.nodes.push(self.nodes[to_us].clone());
                    local_idx.insert(to_us, li);
                    queue.push_back((to_us, depth + 1));
                }
            }
            // Reverse edges.
            for &ei in self.reverse_neighbors(current as ConceptIdx) {
                let (from, _, _) = self.edges[ei];
                let from_us = from as usize;
                if visited.insert(from_us) {
                    let li = sub.nodes.len();
                    sub.nodes.push(self.nodes[from_us].clone());
                    local_idx.insert(from_us, li);
                    queue.push_back((from_us, depth + 1));
                }
            }
        }
        // Add edges where both endpoints are in the subgraph.
        for (from, to, edge) in &self.edges {
            let from_us = *from as usize;
            let to_us = *to as usize;
            if let (Some(&fl), Some(&tl)) = (local_idx.get(&from_us), local_idx.get(&to_us)) {
                sub.edges.push((fl, tl, edge.clone()));
            }
        }
        sub
    }

    /// Find all connected components via DFS over undirected edges.
    ///
    /// Returns a vector of components, each a sorted vector of node indices.
    pub fn connected_components(&self) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let mut visited = vec![false; n];
        let mut components = Vec::new();

        for start in 0..n {
            if visited[start] {
                continue;
            }
            let mut component = Vec::new();
            let mut stack = vec![start];
            while let Some(cur) = stack.pop() {
                if visited[cur] {
                    continue;
                }
                visited[cur] = true;
                component.push(cur);
                // Forward neighbors.
                for &ei in self.neighbors(cur as ConceptIdx) {
                    let (_, to, _) = self.edges[ei];
                    if !visited[to as usize] {
                        stack.push(to as usize);
                    }
                }
                // Reverse neighbors.
                for &ei in self.reverse_neighbors(cur as ConceptIdx) {
                    let (from, _, _) = self.edges[ei];
                    if !visited[from as usize] {
                        stack.push(from as usize);
                    }
                }
            }
            component.sort_unstable();
            components.push(component);
        }
        components
    }
}

// ---------------------------------------------------------------------------
// Automated graph construction
// ---------------------------------------------------------------------------

/// Classify whether an expression represents a theorem type (has Pi/forall
/// at the top level) vs a structure/definition.
fn classify_expr(exprs: &[FlatExpr], type_idx: ExprIdx) -> bool {
    let Some(e) = exprs.get(type_idx as usize) else {
        return false;
    };
    e.tag == FlatTag::Pi as u8
}

/// Build a `ConceptGraph` automatically from raw library data.
///
/// Creates nodes for all constants (classifying Theorem vs Structure based on
/// expression structure), adds `DependsOn` edges from the dependency adjacency
/// list, and detects cross-system `Equivalent` edges via `EquivalenceDetector`.
pub fn build_from_library(
    constants: &[MathverseConstantHeader],
    strings: &[String],
    exprs: &[FlatExpr],
    deps: &[Vec<u32>],
) -> ConceptGraph {
    let mut graph = ConceptGraph::new();

    // Phase 1: create nodes.
    for (i, header) in constants.iter().enumerate() {
        let name = strings
            .get(header.name_idx as usize)
            .cloned()
            .unwrap_or_default();
        let is_theorem = classify_expr(exprs, header.type_idx);
        let node = if is_theorem {
            ConceptNode::Theorem {
                constant_idx: i as ConstantIdx,
            }
        } else {
            ConceptNode::Structure {
                name: name.clone(),
                axioms: Vec::new(),
            }
        };
        let concept_idx = graph.add_named_node(&name, node);
        graph.register_constant(i as ConstantIdx, concept_idx);
    }

    // Phase 2: add DependsOn edges from the adjacency list.
    for (from, dep_list) in deps.iter().enumerate() {
        if from >= constants.len() {
            break;
        }
        let from_concept = match graph.lookup_constant(from as ConstantIdx) {
            Some(idx) => idx,
            None => continue,
        };
        for &to in dep_list {
            if let Some(to_concept) = graph.lookup_constant(to) {
                graph.add_edge(from_concept, to_concept, ConceptEdge::DependsOn);
            }
        }
    }

    // Phase 3: detect cross-system equivalences.
    let mut detector = EquivalenceDetector::new();
    for (i, header) in constants.iter().enumerate() {
        let name = strings
            .get(header.name_idx as usize)
            .map(|s| s.as_str())
            .unwrap_or("");
        let source = header.source().unwrap_or(SourceSystem::Lean4);
        detector.index_constant(i as ConstantIdx, name, source, exprs, header.type_idx);
    }
    let equiv_pairs = detector.detect_all(0.7);
    for (a, b, _confidence) in &equiv_pairs {
        if let (Some(ca), Some(cb)) = (graph.lookup_constant(*a), graph.lookup_constant(*b)) {
            graph.add_edge(ca, cb, ConceptEdge::Equivalent { proof: None });
        }
    }

    graph
}

// ---------------------------------------------------------------------------
// DomainIndex
// ---------------------------------------------------------------------------

/// Domain-specific index for efficient classification-based lookups.
///
/// Maps complexity class names and MSC 2020 codes to sets of graph node
/// indices, enabling O(1) lookup for domain queries.
#[derive(Clone, Debug, Default)]
pub struct DomainIndex {
    /// Complexity class name -> node indices (e.g. "P" -> [0, 5, 12]).
    pub complexity_classes: hashbrown::HashMap<String, Vec<usize>>,
    /// MSC 2020 classification codes -> node indices (e.g. "11A" -> [3, 7]).
    pub msc_codes: hashbrown::HashMap<String, Vec<usize>>,
}

/// Known MSC 2020 classification prefixes for heuristic tagging.
const MSC_PREFIXES: &[(&str, &str)] = &[
    ("Nat", "11"),   // Number theory
    ("Int", "11"),   // Number theory
    ("Group", "20"), // Group theory
    ("Ring", "13"),  // Commutative algebra
    ("Field", "12"), // Field theory
    ("Topology", "54"),
    ("Metric", "54"),
    ("Measure", "28"),
    ("Probability", "60"),
    ("Order", "06"),
    ("Lattice", "06"),
    ("Category", "18"),
    ("Linear", "15"), // Linear algebra
    ("Matrix", "15"),
    ("Polynomial", "13"),
    ("Set", "03"), // Logic and foundations
    ("Logic", "03"),
    ("Bool", "03"),
    ("Complex", "30"),
    ("Real", "26"), // Real analysis
    ("List", "68"), // Computer science
    ("Array", "68"),
    ("Graph", "05"), // Combinatorics
    ("Finset", "05"),
];

/// Known complexity class keywords for heuristic tagging.
const COMPLEXITY_KEYWORDS: &[&str] = &[
    "PSPACE", "NP", "CONP", "EXPTIME", "NEXPTIME", "BPP", "BQP", "PPAD", "NC", "DTIME", "NTIME",
];

/// Build a `DomainIndex` from a `ConceptGraph` and the library string table.
///
/// Uses heuristic name matching to assign MSC codes and complexity class
/// tags to graph nodes.
pub fn build_domain_index(graph: &ConceptGraph, strings: &[String]) -> DomainIndex {
    let mut index = DomainIndex::default();

    for (node_idx, node) in graph.nodes.iter().enumerate() {
        let name = match node {
            ConceptNode::Theorem { constant_idx } => strings
                .get(*constant_idx as usize)
                .map(|s| s.as_str())
                .unwrap_or(""),
            ConceptNode::Structure { name, .. } => name.as_str(),
            ConceptNode::ComplexityClass { name, .. } => {
                index
                    .complexity_classes
                    .entry(name.clone())
                    .or_default()
                    .push(node_idx);
                name.as_str()
            }
            ConceptNode::NNArchPattern { .. } | ConceptNode::Conjecture { .. } => continue,
        };

        // Heuristic MSC code assignment.
        for &(prefix, code) in MSC_PREFIXES {
            if name.contains(prefix) {
                index
                    .msc_codes
                    .entry(code.to_owned())
                    .or_default()
                    .push(node_idx);
                break; // one MSC code per node
            }
        }

        // Heuristic complexity class assignment.
        let upper = name.to_uppercase();
        for &kw in COMPLEXITY_KEYWORDS {
            if upper.contains(kw) {
                index
                    .complexity_classes
                    .entry(kw.to_owned())
                    .or_default()
                    .push(node_idx);
            }
        }
    }

    index
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::search::ConceptEdgeKind;
    use crate::types::{AxiomProfile, ContentDomain, ImportConfidence, NO_VALUE};

    fn thm(c: ConstantIdx) -> ConceptNode {
        ConceptNode::Theorem { constant_idx: c }
    }

    #[test]
    fn test_conjecture_queue_priority_order() {
        let mut q = ConjectureQueue::new();
        q.push(3, 100);
        q.push(1, 200);
        q.push(2, 300);
        q.push(1, 400);
        assert_eq!(q.len(), 4);
        let (p, idx) = q.pop().unwrap();
        assert_eq!(p, 1);
        assert!(idx == 200 || idx == 400);
        let (p, _) = q.pop().unwrap();
        assert_eq!(p, 1);
        let (p, idx) = q.pop().unwrap();
        assert_eq!(p, 2);
        assert_eq!(idx, 300);
        let (p, idx) = q.pop().unwrap();
        assert_eq!(p, 3);
        assert_eq!(idx, 100);
        assert!(q.is_empty());
    }

    #[test]
    fn test_add_node_and_count() {
        let mut g = ConceptGraph::new();
        assert_eq!(g.node_count(), 0);
        let a = g.add_node(thm(10));
        assert_eq!(a, 0);
        assert_eq!(g.node_count(), 1);
        let b = g.add_named_node("GroupTheory", thm(20));
        assert_eq!(b, 1);
        assert_eq!(g.node_count(), 2);
        assert!(g.node(a).is_some());
        assert!(g.node(99).is_none());
    }

    #[test]
    fn test_add_edge_and_adjacency() {
        let mut g = ConceptGraph::new();
        let (a, b, c) = (g.add_node(thm(1)), g.add_node(thm(2)), g.add_node(thm(3)));
        g.add_edge(a, b, ConceptEdge::DependsOn);
        g.add_edge(a, c, ConceptEdge::Generalizes);
        g.add_edge(b, c, ConceptEdge::DependsOn);
        assert_eq!(g.edge_count(), 3);
        assert_eq!(g.neighbors(a).len(), 2);
        assert_eq!(g.neighbors(c).len(), 0);
        assert_eq!(g.reverse_neighbors(c).len(), 2);
        assert_eq!(g.reverse_neighbors(a).len(), 0);
        let e = g.get_edge(0).unwrap();
        assert_eq!(e.0, a);
        assert_eq!(e.1, b);
        assert!(matches!(e.2, ConceptEdge::DependsOn));
        assert!(g.get_edge(99).is_none());
    }

    #[test]
    fn test_name_and_constant_lookup() {
        let mut g = ConceptGraph::new();
        let n = g.add_named_node("FLT", thm(42));
        g.register_constant(42, n);
        assert_eq!(g.lookup_name("FLT"), Some(n));
        assert_eq!(g.lookup_name("missing"), None);
        assert_eq!(g.lookup_constant(42), Some(n));
        assert_eq!(g.lookup_constant(999), None);
    }

    #[test]
    fn test_bfs_with_edge_filter() {
        let mut g = ConceptGraph::new();
        let (a, b, c, d) = (
            g.add_node(thm(1)),
            g.add_node(thm(2)),
            g.add_node(thm(3)),
            g.add_node(thm(4)),
        );
        g.add_edge(a, b, ConceptEdge::DependsOn);
        g.add_edge(b, c, ConceptEdge::DependsOn);
        g.add_edge(a, d, ConceptEdge::Generalizes);

        let filter = EdgeFilter {
            allowed_edges: Some(vec![ConceptEdgeKind::DependsOn]),
            max_depth: None,
        };
        let sub = g.bfs(a, &filter);
        assert_eq!(sub.nodes.len(), 3); // a, b, c (d filtered out)
        assert_eq!(sub.edges.len(), 2);

        let depth_filter = EdgeFilter {
            allowed_edges: None,
            max_depth: Some(1),
        };
        let sub2 = g.bfs(a, &depth_filter);
        assert_eq!(sub2.nodes.len(), 3); // a, b, d (c at depth 2)
    }

    #[test]
    fn test_bfs_empty() {
        let sub = ConceptGraph::new().bfs(0, &EdgeFilter::default());
        assert!(sub.nodes.is_empty());
    }

    #[test]
    fn test_find_path() {
        let mut g = ConceptGraph::new();
        let (a, b, c, d) = (
            g.add_node(thm(1)),
            g.add_node(thm(2)),
            g.add_node(thm(3)),
            g.add_node(thm(4)),
        );
        g.add_edge(a, b, ConceptEdge::DependsOn);
        g.add_edge(b, c, ConceptEdge::DependsOn);
        g.add_edge(a, d, ConceptEdge::Generalizes);
        g.add_edge(d, c, ConceptEdge::DependsOn);

        let path = g.find_path(a, c).unwrap();
        assert_eq!(path.len(), 3);
        assert_eq!(*path.first().unwrap(), a);
        assert_eq!(*path.last().unwrap(), c);
        assert_eq!(g.find_path(a, a).unwrap(), vec![a]);
        assert!(g.find_path(c, a).is_none());
        assert!(g.find_path(99, a).is_none());
    }

    #[test]
    fn test_transitive_deps() {
        let mut g = ConceptGraph::new();
        let (a, b, c, d) = (
            g.add_node(thm(1)),
            g.add_node(thm(2)),
            g.add_node(thm(3)),
            g.add_node(thm(4)),
        );
        g.add_edge(a, b, ConceptEdge::DependsOn);
        g.add_edge(b, c, ConceptEdge::DependsOn);
        g.add_edge(a, d, ConceptEdge::Generalizes);
        let deps = g.transitive_deps(a);
        assert!(deps.contains(&b) && deps.contains(&c));
        assert!(!deps.contains(&d) && !deps.contains(&a));
    }

    #[test]
    fn test_find_equivalents() {
        let mut g = ConceptGraph::new();
        let (a, b, c, d) = (
            g.add_node(thm(1)),
            g.add_node(thm(2)),
            g.add_node(thm(3)),
            g.add_node(thm(4)),
        );
        g.add_edge(a, b, ConceptEdge::Equivalent { proof: Some(100) });
        g.add_edge(c, a, ConceptEdge::Equivalent { proof: None });
        g.add_edge(a, d, ConceptEdge::DependsOn);
        let eq = g.find_equivalents(a);
        assert_eq!(eq.len(), 2);
        assert!(eq
            .iter()
            .any(|(conf, i)| *i == b && *conf == EquivConfidence::ProvedEquivalent));
        assert!(eq
            .iter()
            .any(|(conf, i)| *i == c && *conf == EquivConfidence::ManualReview));
    }

    #[test]
    fn test_json_round_trip() {
        let mut g = ConceptGraph::new();
        let a = g.add_named_node("Nat.add_comm", thm(10));
        let b = g.add_node(thm(20));
        g.add_edge(a, b, ConceptEdge::DependsOn);
        g.register_constant(10, a);
        let restored = ConceptGraph::from_json(&g.to_json().unwrap()).unwrap();
        assert_eq!(restored.node_count(), 2);
        assert_eq!(restored.edge_count(), 1);
        assert_eq!(restored.lookup_name("Nat.add_comm"), Some(a));
        assert_eq!(restored.lookup_constant(10), Some(a));
    }

    #[test]
    fn test_empty_graph_queries() {
        let g = ConceptGraph::new();
        assert_eq!(g.node_count(), 0);
        assert!(g.node(0).is_none());
        assert!(g.lookup_name("x").is_none());
        assert!(g.lookup_constant(0).is_none());
        assert!(g.neighbors(0).is_empty());
        assert!(g.reverse_neighbors(0).is_empty());
        assert!(g.find_path(0, 1).is_none());
        assert!(g.transitive_deps(0).is_empty());
        assert!(g.find_equivalents(0).is_empty());
    }

    // -----------------------------------------------------------------------
    // subgraph_around tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_subgraph_around_basic() {
        let mut g = ConceptGraph::new();
        let a = g.add_node(thm(0));
        let b = g.add_node(thm(1));
        let c = g.add_node(thm(2));
        let d = g.add_node(thm(3));
        g.add_edge(a, b, ConceptEdge::DependsOn);
        g.add_edge(b, c, ConceptEdge::DependsOn);
        g.add_edge(c, d, ConceptEdge::DependsOn);

        let sub = g.subgraph_around(b as usize, 1);
        // Should include b, a (reverse), c (forward) — 3 nodes.
        assert_eq!(sub.nodes.len(), 3);
        // Edges within the subgraph: a->b and b->c.
        assert_eq!(sub.edges.len(), 2);
    }

    #[test]
    fn test_subgraph_around_radius_zero() {
        let mut g = ConceptGraph::new();
        let a = g.add_node(thm(0));
        let _b = g.add_node(thm(1));
        g.add_edge(a, 1, ConceptEdge::DependsOn);

        let sub = g.subgraph_around(a as usize, 0);
        assert_eq!(sub.nodes.len(), 1); // only center
        assert!(sub.edges.is_empty());
    }

    #[test]
    fn test_subgraph_around_out_of_bounds() {
        let g = ConceptGraph::new();
        let sub = g.subgraph_around(999, 2);
        assert!(sub.nodes.is_empty());
    }

    // -----------------------------------------------------------------------
    // connected_components tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_connected_components_single() {
        let mut g = ConceptGraph::new();
        let a = g.add_node(thm(0));
        let b = g.add_node(thm(1));
        g.add_edge(a, b, ConceptEdge::DependsOn);

        let comps = g.connected_components();
        assert_eq!(comps.len(), 1);
        assert_eq!(comps[0], vec![0, 1]);
    }

    #[test]
    fn test_connected_components_multiple() {
        let mut g = ConceptGraph::new();
        let _a = g.add_node(thm(0));
        let _b = g.add_node(thm(1));
        let _c = g.add_node(thm(2));
        let _d = g.add_node(thm(3));
        g.add_edge(0, 1, ConceptEdge::DependsOn);
        g.add_edge(2, 3, ConceptEdge::DependsOn);

        let comps = g.connected_components();
        assert_eq!(comps.len(), 2);
        assert!(comps.iter().any(|c| *c == vec![0, 1]));
        assert!(comps.iter().any(|c| *c == vec![2, 3]));
    }

    #[test]
    fn test_connected_components_empty() {
        let g = ConceptGraph::new();
        assert!(g.connected_components().is_empty());
    }

    #[test]
    fn test_connected_components_isolated_nodes() {
        let mut g = ConceptGraph::new();
        let _a = g.add_node(thm(0));
        let _b = g.add_node(thm(1));
        let _c = g.add_node(thm(2));
        // No edges.
        let comps = g.connected_components();
        assert_eq!(comps.len(), 3);
    }

    // -----------------------------------------------------------------------
    // build_from_library tests
    // -----------------------------------------------------------------------

    fn make_header(name_idx: u32, type_idx: u32, source: SourceSystem) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: source as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    #[test]
    fn test_build_from_library_creates_nodes() {
        // String table: 0="Nat.add", 1="Bool.not"
        let strings = vec!["Nat.add".to_owned(), "Bool.not".to_owned()];
        // Expr arena: 0=Sort, 1=Const(0), 2=Pi(0,1,1)
        let exprs = vec![
            FlatExpr::sort(0),
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::pi(0, 1, 1),
        ];
        // Header 0: type=Pi (theorem), Header 1: type=Sort (structure)
        let constants = vec![
            make_header(0, 2, SourceSystem::Lean4),
            make_header(1, 0, SourceSystem::Lean4),
        ];
        let deps: Vec<Vec<u32>> = vec![vec![1], vec![]];

        let graph = build_from_library(&constants, &strings, &exprs, &deps);
        assert_eq!(graph.node_count(), 2);
        // Node 0 is a theorem (Pi type), node 1 is a structure (Sort type).
        assert!(matches!(graph.node(0), Some(ConceptNode::Theorem { .. })));
        assert!(matches!(graph.node(1), Some(ConceptNode::Structure { .. })));
    }

    #[test]
    fn test_build_from_library_adds_deps_edges() {
        let strings = vec!["a".to_owned(), "b".to_owned(), "c".to_owned()];
        let exprs = vec![FlatExpr::sort(0)];
        let constants = vec![
            make_header(0, 0, SourceSystem::Lean4),
            make_header(1, 0, SourceSystem::Lean4),
            make_header(2, 0, SourceSystem::Lean4),
        ];
        let deps = vec![vec![1, 2], vec![2], vec![]];

        let graph = build_from_library(&constants, &strings, &exprs, &deps);
        assert_eq!(graph.node_count(), 3);
        // a depends on b and c: 2 edges from node 0.
        assert!(graph.edge_count() >= 3); // a->b, a->c, b->c, plus any equiv edges
    }

    #[test]
    fn test_build_from_library_empty() {
        let graph = build_from_library(&[], &[], &[], &[]);
        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn test_build_from_library_cross_system_equivalence() {
        // Two constants from different systems with same name and type.
        let strings = vec![
            "Nat.add_comm".to_owned(),
            "PeanoNat.Nat.add_comm".to_owned(),
        ];
        let exprs = vec![
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::pi(0, 0, 1),
        ];
        let constants = vec![
            make_header(0, 2, SourceSystem::Lean4),
            make_header(1, 2, SourceSystem::Coq),
        ];
        let deps: Vec<Vec<u32>> = vec![vec![], vec![]];

        let graph = build_from_library(&constants, &strings, &exprs, &deps);
        assert_eq!(graph.node_count(), 2);
        // Should have at least one Equivalent edge.
        let equivs = graph.find_equivalents(0);
        assert!(
            !equivs.is_empty(),
            "cross-system constants with matching types should get Equivalent edges"
        );
    }

    // -----------------------------------------------------------------------
    // DomainIndex tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_build_domain_index_msc_codes() {
        let mut g = ConceptGraph::new();
        g.add_named_node("Nat.add_comm", thm(0));
        g.add_named_node("Group.mul_assoc", thm(1));
        g.add_named_node("List.map", thm(2));
        let strings = vec![
            "Nat.add_comm".to_owned(),
            "Group.mul_assoc".to_owned(),
            "List.map".to_owned(),
        ];

        let idx = build_domain_index(&g, &strings);
        // Nat -> MSC "11" (number theory)
        assert!(idx.msc_codes.get("11").is_some());
        assert!(idx.msc_codes["11"].contains(&0));
        // Group -> MSC "20" (group theory)
        assert!(idx.msc_codes.get("20").is_some());
        assert!(idx.msc_codes["20"].contains(&1));
        // List -> MSC "68" (computer science)
        assert!(idx.msc_codes.get("68").is_some());
        assert!(idx.msc_codes["68"].contains(&2));
    }

    #[test]
    fn test_build_domain_index_complexity_classes() {
        let mut g = ConceptGraph::new();
        g.add_named_node("PSPACE_complete_thm", thm(0));
        g.add_named_node("NP_hard_reduction", thm(1));
        g.add_named_node("plain_lemma", thm(2));
        let strings = vec![
            "PSPACE_complete_thm".to_owned(),
            "NP_hard_reduction".to_owned(),
            "plain_lemma".to_owned(),
        ];

        let idx = build_domain_index(&g, &strings);
        assert!(idx.complexity_classes.get("PSPACE").is_some());
        assert!(idx.complexity_classes["PSPACE"].contains(&0));
        assert!(idx.complexity_classes.get("NP").is_some());
        assert!(idx.complexity_classes["NP"].contains(&1));
        // plain_lemma should not be in any complexity class.
        assert!(idx.complexity_classes.values().all(|v| !v.contains(&2)));
    }

    #[test]
    fn test_build_domain_index_empty() {
        let g = ConceptGraph::new();
        let idx = build_domain_index(&g, &[]);
        assert!(idx.msc_codes.is_empty());
        assert!(idx.complexity_classes.is_empty());
    }

    #[test]
    fn test_classify_expr_pi_is_theorem() {
        let exprs = vec![FlatExpr::const_ref(0, u32::MAX), FlatExpr::pi(0, 0, 0)];
        assert!(classify_expr(&exprs, 1));
        assert!(!classify_expr(&exprs, 0));
    }

    #[test]
    fn test_classify_expr_out_of_bounds() {
        assert!(!classify_expr(&[], 999));
    }
}

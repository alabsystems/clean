// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MathverseSearch trait — the retrieval API for the Mathverse Library.

use crate::error::MathverseResult;
use crate::graph_alpha::{ConceptEdge, ConceptGraph, ConceptNode, DomainIndex, EquivConfidence};
use crate::types::{ConceptIdx, ConstantIdx, ContentDomain, ExprIdx, MathverseConstantHeader};

/// Result of a search query.
#[derive(Clone, Debug)]
pub struct SearchResult {
    pub constant_idx: ConstantIdx,
    pub header: MathverseConstantHeader,
    pub score: f32,
}

/// Filter for graph edge traversal.
#[derive(Clone, Debug, Default)]
pub struct EdgeFilter {
    pub allowed_edges: Option<Vec<ConceptEdgeKind>>,
    pub max_depth: Option<u32>,
}

/// Edge kind discriminant (for filtering without payload data).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConceptEdgeKind {
    Generalizes,
    SpecialCase,
    Analogous,
    Equivalent,
    DependsOn,
    InstanceOf,
    ReducesTo,
    Separates,
    CertifiesProperty,
}

impl ConceptEdgeKind {
    pub fn matches(&self, edge: &ConceptEdge) -> bool {
        matches!(
            (self, edge),
            (Self::Generalizes, ConceptEdge::Generalizes)
                | (Self::SpecialCase, ConceptEdge::SpecialCase)
                | (Self::Analogous, ConceptEdge::Analogous { .. })
                | (Self::Equivalent, ConceptEdge::Equivalent { .. })
                | (Self::DependsOn, ConceptEdge::DependsOn)
                | (Self::InstanceOf, ConceptEdge::InstanceOf)
                | (Self::ReducesTo, ConceptEdge::ReducesTo)
                | (Self::Separates, ConceptEdge::Separates)
                | (Self::CertifiesProperty, ConceptEdge::CertifiesProperty)
        )
    }
}

/// Subgraph returned from a graph query.
#[derive(Clone, Debug, Default)]
pub struct SubGraph {
    pub nodes: Vec<ConceptNode>,
    pub edges: Vec<(usize, usize, ConceptEdge)>,
}

/// Domain-specific search query.
#[derive(Clone, Debug)]
pub enum DomainQuery {
    /// Search by complexity class name (e.g., "PSPACE").
    ComplexityClass(String),
    /// Search by NN architecture pattern.
    NNArchitecture(String),
    /// Search by software specification pattern.
    SoftwareSpec(String),
    /// Search by MSC 2020 classification code.
    MscCode(String),
    /// Free-text domain query.
    FreeText(String),
}

/// Iterator over dependency graph edges.
pub struct DependencyIterator {
    stack: Vec<ConstantIdx>,
    visited: hashbrown::HashSet<ConstantIdx>,
}

impl DependencyIterator {
    pub fn new(root: ConstantIdx) -> Self {
        Self {
            stack: vec![root],
            visited: hashbrown::HashSet::new(),
        }
    }

    /// Push a constant index onto the traversal stack.
    ///
    /// Used by `walk_deps` to seed direct dependencies so that the
    /// iterator can yield them (and the caller can extend with transitive
    /// deps by calling `walk_deps` again on each yielded node).
    pub fn push(&mut self, idx: ConstantIdx) {
        if !self.visited.contains(&idx) {
            self.stack.push(idx);
        }
    }
}

impl Iterator for DependencyIterator {
    type Item = ConstantIdx;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(idx) = self.stack.pop() {
            if self.visited.insert(idx) {
                return Some(idx);
            }
        }
        None
    }
}

/// The primary retrieval trait for the Mathverse Library.
///
/// Five search modes, each with a target latency:
/// - Name lookup: <100ns (bloom filter + binary search)
/// - Type-directed: <10us (WHNF-normalized discrimination tree)
/// - Semantic search: <1ms (math-specialized embedding ANN)
/// - Dependency walk: <1us/hop (adjacency list)
/// - Cross-system: <100us (equivalence index)
pub trait MathverseSearch {
    fn lookup_name(&self, name: &str) -> Option<MathverseConstantHeader>;

    fn search_type(
        &self,
        query_type: ExprIdx,
        max_results: usize,
    ) -> MathverseResult<Vec<SearchResult>>;

    fn search_semantic(
        &self,
        query: &str,
        max_results: usize,
    ) -> MathverseResult<Vec<SearchResult>>;

    fn walk_deps(&self, constant: ConstantIdx) -> DependencyIterator;

    fn find_equivalents(
        &self,
        constant: ConstantIdx,
    ) -> MathverseResult<Vec<(EquivConfidence, ConstantIdx)>>;

    fn graph_query(
        &self,
        node: ConstantIdx,
        edge_filter: &EdgeFilter,
        depth: u32,
    ) -> MathverseResult<SubGraph>;

    fn search_domain(
        &self,
        domain: ContentDomain,
        query: &DomainQuery,
    ) -> MathverseResult<Vec<SearchResult>>;
}

// ---------------------------------------------------------------------------
// SearchConfig
// ---------------------------------------------------------------------------

/// Configuration for domain search queries.
#[derive(Clone, Debug)]
pub struct SearchConfig {
    /// Maximum number of results to return.
    pub max_results: usize,
    /// Minimum score threshold for inclusion in results.
    pub min_score: f32,
    /// Whether to include transitive dependencies in results.
    pub include_deps: bool,
    /// Search timeout in milliseconds (0 = no timeout).
    pub search_timeout_ms: u64,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            max_results: 100,
            min_score: 0.0,
            include_deps: false,
            search_timeout_ms: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// RankedResult
// ---------------------------------------------------------------------------

/// A search result with a detailed score breakdown.
#[derive(Clone, Debug)]
pub struct RankedResult {
    /// Index of the node in the concept graph.
    pub node_idx: usize,
    /// Constant index (if the node has one).
    pub constant_idx: Option<ConstantIdx>,
    /// Score from name matching.
    pub name_score: f32,
    /// Score from type/structural matching.
    pub type_score: f32,
    /// Score from domain classification matching.
    pub domain_score: f32,
    /// Combined score (weighted sum).
    pub total_score: f32,
}

impl RankedResult {
    /// Compute a weighted total from component scores.
    pub fn compute_total(name_score: f32, type_score: f32, domain_score: f32) -> f32 {
        name_score * 0.4 + type_score * 0.3 + domain_score * 0.3
    }
}

// ---------------------------------------------------------------------------
// DomainSearchEngine
// ---------------------------------------------------------------------------

/// Domain-specific search engine wrapping a graph and domain index.
///
/// Provides structured queries over the concept graph using domain
/// classifications (MSC codes, complexity classes) and name matching.
pub struct DomainSearchEngine<'a> {
    graph: &'a ConceptGraph,
    domain_index: &'a DomainIndex,
    strings: &'a [String],
    config: SearchConfig,
}

impl<'a> DomainSearchEngine<'a> {
    /// Create a new search engine over the given graph and domain index.
    pub fn new(
        graph: &'a ConceptGraph,
        domain_index: &'a DomainIndex,
        strings: &'a [String],
        config: SearchConfig,
    ) -> Self {
        Self {
            graph,
            domain_index,
            strings,
            config,
        }
    }

    /// Execute a domain query and return ranked results.
    pub fn search(&self, query: &DomainQuery) -> Vec<RankedResult> {
        search_domain_query(
            query,
            self.graph,
            self.domain_index,
            self.strings,
            &self.config,
        )
    }
}

/// Execute a domain query against the graph and domain index.
///
/// Dispatches to the appropriate index (complexity classes, MSC codes, or
/// name-based search) depending on the query variant. Results are sorted
/// by total score descending and capped at `config.max_results`.
pub fn search_domain_query(
    query: &DomainQuery,
    graph: &ConceptGraph,
    domain_idx: &DomainIndex,
    strings: &[String],
    config: &SearchConfig,
) -> Vec<RankedResult> {
    let mut results = Vec::new();

    match query {
        DomainQuery::ComplexityClass(class) => {
            let upper = class.to_uppercase();
            if let Some(nodes) = domain_idx.complexity_classes.get(&upper) {
                for &node_idx in nodes {
                    let result = score_node(node_idx, graph, strings, &upper, 1.0);
                    if result.total_score >= config.min_score {
                        results.push(result);
                    }
                }
            }
        }
        DomainQuery::MscCode(code) => {
            if let Some(nodes) = domain_idx.msc_codes.get(code.as_str()) {
                for &node_idx in nodes {
                    let result = score_node(node_idx, graph, strings, code, 1.0);
                    if result.total_score >= config.min_score {
                        results.push(result);
                    }
                }
            }
        }
        DomainQuery::FreeText(text)
        | DomainQuery::SoftwareSpec(text)
        | DomainQuery::NNArchitecture(text) => {
            let lower = text.to_lowercase();
            for node_idx in 0..graph.node_count() {
                let name = node_name(node_idx, graph, strings);
                let name_lower = name.to_lowercase();
                if name_lower.contains(&lower) {
                    let name_score = if name_lower == lower {
                        1.0
                    } else {
                        lower.len() as f32 / name_lower.len().max(1) as f32
                    };
                    let result = score_node(node_idx, graph, strings, &lower, name_score);
                    if result.total_score >= config.min_score {
                        results.push(result);
                    }
                }
            }
        }
    }

    // Sort by total score descending.
    results.sort_by(|a, b| {
        b.total_score
            .partial_cmp(&a.total_score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    results.truncate(config.max_results);
    results
}

/// Extract the display name for a graph node.
fn node_name<'a>(node_idx: usize, graph: &'a ConceptGraph, strings: &'a [String]) -> &'a str {
    match graph.node(node_idx as ConceptIdx) {
        Some(ConceptNode::Theorem { constant_idx }) => strings
            .get(*constant_idx as usize)
            .map(|s| s.as_str())
            .unwrap_or(""),
        Some(ConceptNode::Structure { name, .. }) => name.as_str(),
        Some(ConceptNode::ComplexityClass { name, .. }) => name.as_str(),
        _ => "",
    }
}

/// Score a single node for a domain query.
fn score_node(
    node_idx: usize,
    graph: &ConceptGraph,
    strings: &[String],
    query: &str,
    domain_score: f32,
) -> RankedResult {
    let name = node_name(node_idx, graph, strings);
    let name_lower = name.to_lowercase();
    let query_lower = query.to_lowercase();

    let name_score = if name_lower == query_lower {
        1.0
    } else if name_lower.contains(&query_lower) {
        0.5 + (query_lower.len() as f32 / name_lower.len().max(1) as f32) * 0.5
    } else {
        0.0
    };

    // Type score based on connectivity (more edges = more important).
    let out_edges = graph.neighbors(node_idx as ConceptIdx).len();
    let in_edges = graph.reverse_neighbors(node_idx as ConceptIdx).len();
    let type_score = ((out_edges + in_edges) as f32).min(10.0) / 10.0;

    let constant_idx = match graph.node(node_idx as ConceptIdx) {
        Some(ConceptNode::Theorem { constant_idx }) => Some(*constant_idx),
        _ => None,
    };

    let total = RankedResult::compute_total(name_score, type_score, domain_score);
    RankedResult {
        node_idx,
        constant_idx,
        name_score,
        type_score,
        domain_score,
        total_score: total,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph_alpha::{build_domain_index, ConceptGraph, DomainIndex};

    fn build_test_graph() -> (ConceptGraph, Vec<String>, DomainIndex) {
        let mut g = ConceptGraph::new();
        g.add_named_node("Nat.add_comm", ConceptNode::Theorem { constant_idx: 0 });
        g.add_named_node("Group.mul_assoc", ConceptNode::Theorem { constant_idx: 1 });
        g.add_named_node("PSPACE_complete", ConceptNode::Theorem { constant_idx: 2 });
        g.add_named_node("List.map_comp", ConceptNode::Theorem { constant_idx: 3 });
        g.add_edge(0, 1, ConceptEdge::DependsOn);
        g.add_edge(2, 3, ConceptEdge::DependsOn);

        let strings = vec![
            "Nat.add_comm".to_owned(),
            "Group.mul_assoc".to_owned(),
            "PSPACE_complete".to_owned(),
            "List.map_comp".to_owned(),
        ];
        let idx = build_domain_index(&g, &strings);
        (g, strings, idx)
    }

    #[test]
    fn test_search_config_defaults() {
        let cfg = SearchConfig::default();
        assert_eq!(cfg.max_results, 100);
        assert!((cfg.min_score - 0.0).abs() < f32::EPSILON);
        assert!(!cfg.include_deps);
        assert_eq!(cfg.search_timeout_ms, 0);
    }

    #[test]
    fn test_ranked_result_compute_total() {
        let total = RankedResult::compute_total(1.0, 0.5, 0.5);
        let expected = 1.0 * 0.4 + 0.5 * 0.3 + 0.5 * 0.3;
        assert!((total - expected).abs() < f32::EPSILON);
    }

    #[test]
    fn test_search_complexity_class() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig::default();
        let results = search_domain_query(
            &DomainQuery::ComplexityClass("PSPACE".to_owned()),
            &g,
            &idx,
            &strings,
            &cfg,
        );
        assert!(!results.is_empty(), "PSPACE query should find results");
        assert!(results.iter().any(|r| r.node_idx == 2));
    }

    #[test]
    fn test_search_msc_code() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig::default();
        let results = search_domain_query(
            &DomainQuery::MscCode("11".to_owned()),
            &g,
            &idx,
            &strings,
            &cfg,
        );
        assert!(!results.is_empty(), "MSC 11 should match Nat");
        assert!(results.iter().any(|r| r.node_idx == 0));
    }

    #[test]
    fn test_search_free_text() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig::default();
        let results = search_domain_query(
            &DomainQuery::FreeText("Group".to_owned()),
            &g,
            &idx,
            &strings,
            &cfg,
        );
        assert!(!results.is_empty());
        assert!(results.iter().any(|r| r.node_idx == 1));
    }

    #[test]
    fn test_search_no_results() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig::default();
        let results = search_domain_query(
            &DomainQuery::FreeText("nonexistent_query_xyz".to_owned()),
            &g,
            &idx,
            &strings,
            &cfg,
        );
        assert!(results.is_empty());
    }

    #[test]
    fn test_search_respects_max_results() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig {
            max_results: 1,
            ..SearchConfig::default()
        };
        let results = search_domain_query(
            &DomainQuery::FreeText("a".to_owned()), // matches multiple
            &g,
            &idx,
            &strings,
            &cfg,
        );
        assert!(results.len() <= 1);
    }

    #[test]
    fn test_search_respects_min_score() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig {
            min_score: 999.0,
            ..SearchConfig::default()
        };
        let results = search_domain_query(
            &DomainQuery::FreeText("Nat".to_owned()),
            &g,
            &idx,
            &strings,
            &cfg,
        );
        assert!(results.is_empty(), "high min_score should filter all");
    }

    #[test]
    fn test_domain_search_engine_wrapper() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig::default();
        let engine = DomainSearchEngine::new(&g, &idx, &strings, cfg);
        let results = engine.search(&DomainQuery::MscCode("20".to_owned()));
        assert!(!results.is_empty(), "MSC 20 should match Group");
        assert!(results.iter().any(|r| r.node_idx == 1));
    }

    #[test]
    fn test_search_results_sorted_by_score() {
        let (g, strings, idx) = build_test_graph();
        let cfg = SearchConfig::default();
        let results = search_domain_query(
            &DomainQuery::FreeText("a".to_owned()),
            &g,
            &idx,
            &strings,
            &cfg,
        );
        for w in results.windows(2) {
            assert!(
                w[0].total_score >= w[1].total_score,
                "results should be sorted descending by score"
            );
        }
    }
}

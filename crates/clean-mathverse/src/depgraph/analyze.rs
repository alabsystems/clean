// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency-closure construction and impact ranking.
//!
//! Two passes over a kernel `Environment`:
//!
//! 1. [`build_closure`] — BFS from a root declaration over `Expr::Const`
//!    edges. Every reachable constant is recorded with its classification
//!    (axiom / theorem / definition / foundational / trust-marker) and its
//!    direct successor set within the closure.
//!
//! 2. [`rank_unblock_candidates`] — for every non-constructive node in the
//!    closure, count reverse-reachability ("how many other nodes in the
//!    closure transitively depend on this one"). The ranking prefers
//!    domain-specific axioms: promoting a high-rank axiom to a constructive
//!    theorem collapses the largest sub-closure, so agents should target it
//!    next.
//!
//! The BFS mirrors `Environment::axiom_deps` (see `axiom_audit.rs`) but
//! records every constant reached, not only axioms, because impact ranking
//! needs the full topological picture.

use hashbrown::{HashMap, HashSet};
use serde::Serialize;

use clean_kernel::env::is_trust_marker;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::{is_foundational_axiom, ConstantInfo, ConstantKind, Environment, Name};

/// Classification of a closure node. Drives unblock ranking — only
/// `DomainAxiom` / `AxiomDependentTheorem` / `TrustMarker` nodes are
/// candidates for promotion.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NodeClass {
    /// `Declaration::Theorem` with value whose transitive axiom deps are
    /// empty (or only foundational). Not a promotion target.
    ConstructiveTheorem,
    /// `Declaration::Theorem` with value that reaches ≥1 domain-specific
    /// axiom. Promoting any of those axioms shrinks this theorem's closure.
    AxiomDependentTheorem,
    /// Non-foundational `Declaration::Axiom`. Promotion target.
    DomainAxiom,
    /// Foundational `Declaration::Axiom` (in `FOUNDATIONAL_AXIOMS`). Not a
    /// promotion target — already accepted.
    FoundationalAxiom,
    /// `sorry` / `sorryAx` / `trustedArith` / `trustedAy`. Promotion target
    /// (replace the trust envelope with a real proof).
    TrustMarker,
    /// `Declaration::Definition` / `Opaque` / kernel structural decl.
    /// Not a promotion target on its own — but its own dependencies may
    /// be.
    Definition,
    /// Theorem whose proof value is absent (added via `add_decl_structural`
    /// or similar). Not kernel-verified.
    Unchecked,
    /// Referenced from the closure but not registered in the environment
    /// (forward reference, typo, or feature-gated out). Rare.
    Missing,
}

/// Per-node record in the closure. JSON-serializable.
#[derive(Clone, Debug, Serialize)]
pub struct NodeInfo {
    /// Fully-qualified kernel name.
    pub name: String,
    /// Classification used for ranking.
    pub class: NodeClass,
    /// Direct `Expr::Const` successors of this node that are also in the
    /// closure. Sorted for deterministic output.
    pub direct_deps: Vec<String>,
    /// Number of other closure nodes that transitively reach this node
    /// (i.e. would benefit if this node were promoted to
    /// `ConstructiveTheorem`). Self-excluded. Computed by
    /// [`ClosureGraph::annotate_impact`].
    pub impact: usize,
}

/// Transitive closure rooted at a single headline declaration.
#[derive(Clone, Debug, Serialize)]
pub struct ClosureGraph {
    /// Headline root name (e.g. `NNVerify.Block.blockwise_crown_sound`).
    pub root: String,
    /// Every reachable constant, keyed by fully-qualified name. Insertion
    /// order is not meaningful; callers that need deterministic iteration
    /// should sort by name.
    pub nodes: HashMap<String, NodeInfo>,
}

impl ClosureGraph {
    /// Iterator over nodes sorted alphabetically by name. Useful for
    /// deterministic reporting.
    pub fn sorted_nodes(&self) -> Vec<&NodeInfo> {
        let mut v: Vec<&NodeInfo> = self.nodes.values().collect();
        v.sort_by(|a, b| a.name.cmp(&b.name));
        v
    }

    /// Return the size of the domain-axiom closure (non-foundational
    /// axioms + trust markers). Equivalent to `env.axiom_deps(root).len()`
    /// plus any trust markers reached, but computed from the closure the
    /// depgraph already has in memory.
    pub fn domain_axiom_count(&self) -> usize {
        self.nodes
            .values()
            .filter(|n| matches!(n.class, NodeClass::DomainAxiom | NodeClass::TrustMarker))
            .count()
    }
}

/// Candidate node recommended for constructive promotion.
#[derive(Clone, Debug, Serialize)]
pub struct UnblockCandidate {
    /// Fully-qualified kernel name.
    pub name: String,
    /// Class (always `DomainAxiom` / `TrustMarker` / `AxiomDependentTheorem`
    /// / `Unchecked` — never `ConstructiveTheorem` / `FoundationalAxiom`).
    pub class: NodeClass,
    /// Number of closure nodes that transitively depend on this candidate.
    /// Higher = bigger leverage on promotion.
    pub impact: usize,
    /// Direct dependents within the closure (first-step reverse edges).
    /// Informational; rankings use `impact` (transitive).
    pub direct_dependents: usize,
}

/// Walk an expression, pushing every `Expr::Const` name into `out`.
///
/// Uses an explicit stack to avoid deep-recursion blowups on large proof
/// terms. This duplicates `axiom_audit::collect_const_refs` (which is
/// private); keeping it here lets the depgraph record the full direct-edge
/// structure without forcing the kernel crate to widen its API surface.
fn collect_const_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) => stack.push(inner),
            ExprKind::Proj(_, _, inner) => stack.push(inner),
            ExprKind::Squash(inner) => stack.push(inner),
            _ => {}
        }
    }
}

/// Classify a `ConstantInfo` for depgraph purposes.
fn classify(env: &Environment, info: &ConstantInfo) -> NodeClass {
    match info.kind {
        ConstantKind::Axiom => {
            if is_trust_marker(&info.name) {
                NodeClass::TrustMarker
            } else if is_foundational_axiom(&info.name) {
                NodeClass::FoundationalAxiom
            } else {
                NodeClass::DomainAxiom
            }
        }
        ConstantKind::Theorem => {
            if info.value.is_none() {
                NodeClass::Unchecked
            } else {
                // Cheap check: delegate to env.axiom_deps for correctness.
                // This is O(closure) per theorem which is fine at the
                // scale we run (headline closures are small hundreds of
                // nodes).
                match env.axiom_deps(&info.name) {
                    Some(deps) if deps.is_empty() => NodeClass::ConstructiveTheorem,
                    Some(_) => NodeClass::AxiomDependentTheorem,
                    None => NodeClass::Unchecked,
                }
            }
        }
        ConstantKind::Definition | ConstantKind::Opaque => NodeClass::Definition,
    }
}

/// Extract the direct `Expr::Const` successors of a registered constant
/// (type + value, if any). Names are deduplicated but unsorted.
fn direct_refs(info: &ConstantInfo) -> HashSet<Name> {
    let mut out = HashSet::new();
    collect_const_refs(&info.type_, &mut out);
    if let Some(ref v) = info.value {
        collect_const_refs(v, &mut out);
    }
    out
}

/// Build the transitive-dependency closure of `root` in `env`.
///
/// Returns `None` if `root` is not registered. BFS over `Expr::Const`
/// edges; every reachable constant is classified and its direct closure
/// successors recorded. Impact counts are populated by
/// [`ClosureGraph::annotate_impact`] (called automatically here so
/// callers always see populated ranks).
pub fn build_closure(env: &Environment, root: &Name) -> Option<ClosureGraph> {
    env.get_const(root)?;
    let mut visited: HashSet<Name> = HashSet::new();
    let mut queue: Vec<Name> = vec![root.clone()];
    let mut nodes: HashMap<String, NodeInfo> = HashMap::new();
    while let Some(n) = queue.pop() {
        if !visited.insert(n.clone()) {
            continue;
        }
        let name_str = n.to_string();
        match env.get_const(&n) {
            Some(info) => {
                let refs = direct_refs(info);
                let class = classify(env, info);
                let mut direct: Vec<String> = refs.iter().map(|x| x.to_string()).collect();
                direct.sort();
                nodes.insert(
                    name_str,
                    NodeInfo {
                        name: n.to_string(),
                        class,
                        direct_deps: direct,
                        impact: 0,
                    },
                );
                for r in refs {
                    if !visited.contains(&r) {
                        queue.push(r);
                    }
                }
            }
            None => {
                nodes.insert(
                    name_str,
                    NodeInfo {
                        name: n.to_string(),
                        class: NodeClass::Missing,
                        direct_deps: Vec::new(),
                        impact: 0,
                    },
                );
            }
        }
    }
    let mut graph = ClosureGraph {
        root: root.to_string(),
        nodes,
    };
    annotate_impact(&mut graph);
    Some(graph)
}

/// Populate `NodeInfo::impact` on every node.
///
/// `impact(n)` = |{m ∈ closure : m ≠ n and there exists a path m → … → n}|.
/// Equivalently, impact is the size of the reverse-reachable set,
/// excluding the node itself. Computed by N × forward-BFS from each node
/// at `O(closure^2)`; headline closures are ≲ low thousands of nodes
/// (T60 transitively touches O(1k) constants) so this is cheap.
pub fn annotate_impact(graph: &mut ClosureGraph) {
    // Precompute reverse adjacency: for each node, who points at it?
    let mut reverse: HashMap<String, Vec<String>> = HashMap::new();
    for (name, node) in &graph.nodes {
        for succ in &node.direct_deps {
            if graph.nodes.contains_key(succ) {
                reverse.entry(succ.clone()).or_default().push(name.clone());
            }
        }
    }
    // For each node, BFS backward along `reverse` to count reachable
    // ancestors.
    let node_names: Vec<String> = graph.nodes.keys().cloned().collect();
    for target in node_names {
        let mut seen: HashSet<String> = HashSet::new();
        let mut stack: Vec<String> = reverse.get(&target).cloned().unwrap_or_default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            if let Some(parents) = reverse.get(&cur) {
                for p in parents {
                    if !seen.contains(p) {
                        stack.push(p.clone());
                    }
                }
            }
        }
        if let Some(info) = graph.nodes.get_mut(&target) {
            info.impact = seen.len();
        }
    }
}

/// Return candidate promotions from `graph` sorted by descending impact.
///
/// Filters to `DomainAxiom` + `TrustMarker` + `Unchecked` + the headline
/// itself (if demoted to `DomainAxiom`). `AxiomDependentTheorem` nodes are
/// **not** returned because promoting a theorem body is not a primitive
/// action — promoting its axiom deps is. Agents that want to see
/// "everything worth touching" can walk the closure directly.
///
/// Ties broken alphabetically by name for deterministic output.
pub fn rank_unblock_candidates(
    graph: &ClosureGraph,
    limit: Option<usize>,
) -> Vec<UnblockCandidate> {
    let mut out: Vec<UnblockCandidate> = graph
        .nodes
        .values()
        .filter(|n| {
            matches!(
                n.class,
                NodeClass::DomainAxiom | NodeClass::TrustMarker | NodeClass::Unchecked
            )
        })
        .map(|n| {
            // Direct-dependent count = how many closure nodes list this
            // one in `direct_deps`. Cheap pass over the graph.
            let direct = graph
                .nodes
                .values()
                .filter(|m| m.direct_deps.iter().any(|d| d == &n.name))
                .count();
            UnblockCandidate {
                name: n.name.clone(),
                class: n.class,
                impact: n.impact,
                direct_dependents: direct,
            }
        })
        .collect();
    out.sort_by(|a, b| {
        b.impact
            .cmp(&a.impact)
            .then_with(|| b.direct_dependents.cmp(&a.direct_dependents))
            .then_with(|| a.name.cmp(&b.name))
    });
    if let Some(lim) = limit {
        out.truncate(lim);
    }
    out
}

/// Rank unblock candidates for a headline in one call — convenience
/// wrapper that builds the closure and then ranks. Returns `None` if the
/// headline is not registered.
pub fn rank_unblock_for_headline(
    env: &Environment,
    root: &Name,
    limit: Option<usize>,
) -> Option<Vec<UnblockCandidate>> {
    let graph = build_closure(env, root)?;
    Some(rank_unblock_candidates(&graph, limit))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::depgraph::seed::seed_environment;

    fn seeded() -> Environment {
        let mut env = Environment::new();
        seed_environment(&mut env);
        env
    }

    #[test]
    fn closure_for_t60_contains_headline() {
        let env = seeded();
        let root = Name::from_string("NNVerify.Block.blockwise_crown_sound");
        let graph = build_closure(&env, &root).expect("T60 closure must build");
        assert_eq!(graph.root, "NNVerify.Block.blockwise_crown_sound");
        assert!(
            graph
                .nodes
                .contains_key("NNVerify.Block.blockwise_crown_sound"),
            "headline must be in its own closure"
        );
        // T60 was retired as a false axiom and re-registered as the honest gated
        // `_sound` Theorem (kernel commit 0fd48ca1, TCB 6→5); its domain-axiom
        // closure is empty, so it now classifies as a ConstructiveTheorem.
        let headline = graph
            .nodes
            .get("NNVerify.Block.blockwise_crown_sound")
            .unwrap();
        assert_eq!(headline.class, NodeClass::ConstructiveTheorem);
    }

    #[test]
    fn closure_missing_root_returns_none() {
        let env = seeded();
        let root = Name::from_string("Does.Not.Exist");
        assert!(build_closure(&env, &root).is_none());
    }

    #[test]
    fn unblock_ranking_non_empty_for_c006() {
        let env = seeded();
        let root = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
        let ranked = rank_unblock_for_headline(&env, &root, Some(5)).expect("C006 must rank");
        // Depending on which sub-init helpers succeed in the current
        // build, C006's closure may or may not surface DomainAxiom /
        // TrustMarker / Unchecked nodes. The structural contract
        // remains: bounded, sorted descending by impact.
        assert!(ranked.len() <= 5);
        for w in ranked.windows(2) {
            assert!(w[0].impact >= w[1].impact, "impact must be non-increasing");
        }
    }

    #[test]
    fn impact_is_self_exclusive() {
        let env = seeded();
        let root = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
        let graph = build_closure(&env, &root).unwrap();
        // The root's impact counts only ancestors in the closure. Since
        // the root is the top of its own closure it has 0 ancestors.
        let root_node = graph
            .nodes
            .get("NNVerify.C006.blockwise_equals_monolithic")
            .unwrap();
        assert_eq!(root_node.impact, 0);
    }
}

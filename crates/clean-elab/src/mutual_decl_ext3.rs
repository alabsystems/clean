// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended mutual declaration elaboration (phase 3): cycle classification,
//! optimal elaboration ordering, type dependency tracking, stratification
//! analysis, size estimation, signature consistency, and DOT visualization.
//!
//! Builds on [`mutual_decl`], [`mutual_decl_ext`], and [`mutual_decl_ext2`].

use crate::dep_graph::DependencyGraph;
use crate::error::ElabError;
use crate::mutual_decl::MutualBlock;
use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;

/// Configuration for phase-3 mutual declaration analysis.
#[derive(Debug, Clone)]
pub(crate) struct MutualDeclExt3Config {
    pub(crate) max_declarations: usize,
    pub(crate) max_cycle_report_len: usize,
    pub(crate) size_warning_threshold: usize,
}

impl Default for MutualDeclExt3Config {
    fn default() -> Self {
        Self {
            max_declarations: 128,
            max_cycle_report_len: 32,
            size_warning_threshold: 10_000,
        }
    }
}

// ─── Cycle analysis ─────────────────────────────────────────────────────────

/// Classification of a cycle within a mutual declaration group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CycleKind {
    SelfLoop,
    Binary,
    Complex { len: usize },
}

/// A detected cycle with its participating declaration indices and kind.
#[derive(Debug, Clone)]
pub(crate) struct CycleInfo {
    pub(crate) indices: Vec<usize>,
    pub(crate) kind: CycleKind,
    pub(crate) names: Vec<String>,
}

/// Find and classify all cycles via SCC decomposition.
#[must_use]
pub(crate) fn find_cycles(block: &MutualBlock) -> Vec<CycleInfo> {
    let n = block.declarations.len();
    if n == 0 {
        return Vec::new();
    }
    let sccs = block.dep_graph.compute_sccs(n);
    let mut cycles = Vec::new();
    for scc in &sccs {
        let filtered: Vec<usize> = scc.iter().copied().filter(|&i| i < n).collect();
        if filtered.len() > 1 {
            let kind = if filtered.len() == 2 {
                CycleKind::Binary
            } else {
                CycleKind::Complex {
                    len: filtered.len(),
                }
            };
            let names = filtered
                .iter()
                .map(|&i| block.declarations[i].name.clone())
                .collect();
            cycles.push(CycleInfo {
                indices: filtered,
                kind,
                names,
            });
        } else if filtered.len() == 1 {
            let idx = filtered[0];
            if block
                .dep_graph
                .edges
                .iter()
                .any(|&(f, t)| f == idx && t == idx)
            {
                cycles.push(CycleInfo {
                    indices: vec![idx],
                    kind: CycleKind::SelfLoop,
                    names: vec![block.declarations[idx].name.clone()],
                });
            }
        }
    }
    cycles
}

// ─── Declaration ordering ───────────────────────────────────────────────────

/// Compute optimal elaboration order minimizing forward references.
///
/// Dependencies processed first; within SCCs, indices sorted numerically.
pub(crate) fn compute_elaboration_order(block: &MutualBlock) -> Result<Vec<usize>, ElabError> {
    let n = block.declarations.len();
    if n == 0 {
        return Ok(Vec::new());
    }
    let sccs = block.dep_graph.compute_sccs(n);
    let mut node_to_scc = vec![0usize; n];
    for (si, scc) in sccs.iter().enumerate() {
        for &node in scc {
            if node < n {
                node_to_scc[node] = si;
            }
        }
    }
    let num_sccs = sccs.len();
    let mut cond = DependencyGraph::new();
    for &(from, to) in &block.dep_graph.edges {
        if from < n && to < n {
            let (sf, st) = (node_to_scc[from], node_to_scc[to]);
            if sf != st {
                cond.add_edge(st, sf);
            }
        }
    }
    let scc_order = cond
        .topological_sort(num_sccs)
        .unwrap_or_else(|_| (0..num_sccs).collect());
    let mut result = Vec::with_capacity(n);
    for si in scc_order {
        let mut indices: Vec<usize> = sccs[si].iter().copied().filter(|&i| i < n).collect();
        indices.sort_unstable();
        result.extend(indices);
    }
    Ok(result)
}

/// Count forward references for a given declaration ordering.
#[must_use]
pub(crate) fn count_forward_refs(block: &MutualBlock, order: &[usize]) -> usize {
    let n = block.declarations.len();
    let mut pos_of = vec![0usize; n];
    for (pos, &idx) in order.iter().enumerate() {
        if idx < n {
            pos_of[idx] = pos;
        }
    }
    block
        .dep_graph
        .edges
        .iter()
        .filter(|&&(from, to)| from < n && to < n && pos_of[from] < pos_of[to])
        .count()
}

// ─── Type dependency tracking ───────────────────────────────────────────────

/// Type dependencies for a single declaration.
#[derive(Debug, Clone)]
pub(crate) struct TypeDependency {
    pub(crate) decl_index: usize,
    pub(crate) decl_name: String,
    pub(crate) type_refs: Vec<String>,
    pub(crate) body_refs: Vec<String>,
}

/// Collect type and body constant references for each declaration.
#[must_use]
pub(crate) fn collect_type_dependencies(block: &MutualBlock) -> Vec<TypeDependency> {
    block
        .declarations
        .iter()
        .enumerate()
        .map(|(idx, entry)| {
            let mut type_refs = Vec::new();
            if let Some(ty) = &entry.ty {
                collect_const_names(ty, &mut type_refs);
            }
            let mut body_refs = Vec::new();
            collect_const_names(&entry.body, &mut body_refs);
            TypeDependency {
                decl_index: idx,
                decl_name: entry.name.clone(),
                type_refs,
                body_refs,
            }
        })
        .collect()
}

fn collect_const_names(expr: &Expr, out: &mut Vec<String>) {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if !out.contains(&s) {
                out.push(s);
            }
        }
        ExprKind::App(f, a) => {
            collect_const_names(f, out);
            collect_const_names(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_const_names(ty, out);
            collect_const_names(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_const_names(ty, out);
            collect_const_names(val, out);
            collect_const_names(body, out);
        }
        ExprKind::MData(_, e) | ExprKind::Proj(_, _, e) => collect_const_names(e, out),
        _ => {}
    }
}

// ─── Stratification analysis ────────────────────────────────────────────────

/// An independent layer in a stratified mutual block.
#[derive(Debug, Clone)]
pub(crate) struct StratificationLayer {
    pub(crate) layer_index: usize,
    pub(crate) decl_indices: Vec<usize>,
    pub(crate) decl_names: Vec<String>,
}

/// Result of stratification analysis.
#[derive(Debug, Clone)]
pub(crate) struct StratificationResult {
    pub(crate) layers: Vec<StratificationLayer>,
    pub(crate) is_stratifiable: bool,
    pub(crate) num_components: usize,
}

/// Detect if a mutual group can be stratified into independent layers
/// via connected-component analysis (undirected reachability).
#[must_use]
pub(crate) fn analyze_stratification(block: &MutualBlock) -> StratificationResult {
    let n = block.declarations.len();
    if n == 0 {
        return StratificationResult {
            layers: Vec::new(),
            is_stratifiable: true,
            num_components: 0,
        };
    }
    // Union-Find.
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], x: usize) -> usize {
        let mut root = x;
        while parent[root] != root {
            root = parent[root];
        }
        let mut cur = x;
        while cur != root {
            let next = parent[cur];
            parent[cur] = root;
            cur = next;
        }
        root
    }
    fn union(parent: &mut [usize], a: usize, b: usize) {
        let (ra, rb) = (find(parent, a), find(parent, b));
        if ra != rb {
            parent[ra] = rb;
        }
    }
    for &(from, to) in &block.dep_graph.edges {
        if from < n && to < n {
            union(&mut parent, from, to);
        }
    }
    let mut components: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..n {
        components.entry(find(&mut parent, i)).or_default().push(i);
    }
    let mut layers: Vec<StratificationLayer> = components
        .into_values()
        .enumerate()
        .map(|(li, mut indices)| {
            indices.sort_unstable();
            let names = indices
                .iter()
                .map(|&i| block.declarations[i].name.clone())
                .collect();
            StratificationLayer {
                layer_index: li,
                decl_indices: indices,
                decl_names: names,
            }
        })
        .collect();
    layers.sort_by_key(|l| l.decl_indices.first().copied().unwrap_or(0));
    for (i, layer) in layers.iter_mut().enumerate() {
        layer.layer_index = i;
    }
    let num_components = layers.len();
    StratificationResult {
        layers,
        is_stratifiable: num_components > 1,
        num_components,
    }
}

// ─── Size estimation ────────────────────────────────────────────────────────

/// Size estimate for a single declaration.
#[derive(Debug, Clone)]
pub(crate) struct DeclSizeEstimate {
    pub(crate) index: usize,
    pub(crate) name: String,
    pub(crate) type_nodes: usize,
    pub(crate) body_nodes: usize,
    pub(crate) total: usize,
}

/// Size estimate for the entire mutual block.
#[derive(Debug, Clone)]
pub(crate) struct BlockSizeEstimate {
    pub(crate) declarations: Vec<DeclSizeEstimate>,
    pub(crate) total_nodes: usize,
    pub(crate) exceeds_threshold: bool,
}

fn count_expr_nodes(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::App(f, a) => 1 + count_expr_nodes(f) + count_expr_nodes(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            1 + count_expr_nodes(ty) + count_expr_nodes(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            1 + count_expr_nodes(ty) + count_expr_nodes(val) + count_expr_nodes(body)
        }
        ExprKind::MData(_, e) | ExprKind::Proj(_, _, e) => 1 + count_expr_nodes(e),
        _ => 1,
    }
}

/// Estimate total code size of a mutual group.
#[must_use]
pub(crate) fn estimate_block_size(
    block: &MutualBlock,
    config: &MutualDeclExt3Config,
) -> BlockSizeEstimate {
    let declarations: Vec<DeclSizeEstimate> = block
        .declarations
        .iter()
        .enumerate()
        .map(|(idx, entry)| {
            let type_nodes = entry.ty.as_ref().map(count_expr_nodes).unwrap_or(0);
            let body_nodes = count_expr_nodes(&entry.body);
            DeclSizeEstimate {
                index: idx,
                name: entry.name.clone(),
                type_nodes,
                body_nodes,
                total: type_nodes + body_nodes,
            }
        })
        .collect();
    let total_nodes: usize = declarations.iter().map(|d| d.total).sum();
    BlockSizeEstimate {
        declarations,
        total_nodes,
        exceeds_threshold: total_nodes > config.size_warning_threshold,
    }
}

// ─── Signature analysis ─────────────────────────────────────────────────────

/// Result of analyzing a single declaration's type signature.
#[derive(Debug, Clone)]
pub(crate) struct SignatureInfo {
    pub(crate) index: usize,
    pub(crate) name: String,
    pub(crate) num_params: usize,
    pub(crate) has_explicit_type: bool,
    pub(crate) return_sort_level: Option<u32>,
}

/// Result of analyzing type signatures across a mutual group.
#[derive(Debug, Clone)]
pub(crate) struct SignatureAnalysis {
    pub(crate) signatures: Vec<SignatureInfo>,
    pub(crate) uniform_arity: bool,
    pub(crate) missing_type_count: usize,
}

fn count_pi_params(expr: &Expr) -> usize {
    let (mut count, mut current) = (0, expr);
    while let ExprKind::Pi(_, _, body) = current.kind() {
        count += 1;
        current = body;
    }
    count
}

fn return_sort_level(expr: &Expr) -> Option<u32> {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    if let ExprKind::Sort(level) = current.kind() {
        return level_to_nat(level);
    }
    None
}

fn level_to_nat(level: &clean_kernel::Level) -> Option<u32> {
    match level {
        clean_kernel::Level::Zero => Some(0),
        clean_kernel::Level::Succ(inner) => level_to_nat(inner).map(|n| n + 1),
        _ => None,
    }
}

/// Analyze type signatures across a mutual group for consistency.
#[must_use]
pub(crate) fn analyze_signatures(block: &MutualBlock) -> SignatureAnalysis {
    let signatures: Vec<SignatureInfo> = block
        .declarations
        .iter()
        .enumerate()
        .map(|(idx, entry)| {
            let (num_params, has_type, sort_level) = match &entry.ty {
                Some(ty) => (count_pi_params(ty), true, return_sort_level(ty)),
                None => (0, false, None),
            };
            SignatureInfo {
                index: idx,
                name: entry.name.clone(),
                num_params,
                has_explicit_type: has_type,
                return_sort_level: sort_level,
            }
        })
        .collect();
    let typed_arities: Vec<usize> = signatures
        .iter()
        .filter(|s| s.has_explicit_type)
        .map(|s| s.num_params)
        .collect();
    let uniform_arity = typed_arities.len() <= 1 || typed_arities.windows(2).all(|w| w[0] == w[1]);
    let missing_type_count = signatures.iter().filter(|s| !s.has_explicit_type).count();
    SignatureAnalysis {
        signatures,
        uniform_arity,
        missing_type_count,
    }
}

// ─── DOT visualization ──────────────────────────────────────────────────────

/// Generate a DOT format graph of mutual declaration dependencies.
#[must_use]
pub(crate) fn to_dot(block: &MutualBlock) -> String {
    let n = block.declarations.len();
    let mut out = String::with_capacity(256);
    let _ = writeln!(out, "digraph mutual_decls {{");
    let _ = writeln!(out, "  rankdir=LR;");
    for (idx, entry) in block.declarations.iter().enumerate() {
        let shape = if entry.is_noncomputable {
            "box"
        } else {
            "ellipse"
        };
        let _ = writeln!(out, "  n{idx} [label=\"{}\", shape={shape}];", entry.name);
    }
    let mut seen_edges = HashSet::new();
    for &(from, to) in &block.dep_graph.edges {
        if from < n && to < n && seen_edges.insert((from, to)) {
            let style = if from == to { "dotted" } else { "solid" };
            let _ = writeln!(out, "  n{from} -> n{to} [style={style}];");
        }
    }
    let _ = writeln!(out, "}}");
    out
}

// ─── Full phase-3 analysis ──────────────────────────────────────────────────

/// Full phase-3 analysis result.
#[derive(Debug, Clone)]
pub(crate) struct MutualDeclExt3Result {
    pub(crate) cycles: Vec<CycleInfo>,
    pub(crate) elaboration_order: Vec<usize>,
    pub(crate) forward_ref_count: usize,
    pub(crate) type_dependencies: Vec<TypeDependency>,
    pub(crate) stratification: StratificationResult,
    pub(crate) size_estimate: BlockSizeEstimate,
    pub(crate) signature_analysis: SignatureAnalysis,
}

/// Perform full phase-3 analysis on a mutual block.
pub(crate) fn analyze_mutual_block_ext3(
    block: &MutualBlock,
    config: &MutualDeclExt3Config,
) -> Result<MutualDeclExt3Result, ElabError> {
    let n = block.declarations.len();
    if n > config.max_declarations {
        return Err(ElabError::Unsupported {
            feature: format!(
                "mutual block with {} declarations exceeds limit of {}",
                n, config.max_declarations
            ),
        });
    }
    let cycles = find_cycles(block);
    let elaboration_order = compute_elaboration_order(block)?;
    let forward_ref_count = count_forward_refs(block, &elaboration_order);
    let type_dependencies = collect_type_dependencies(block);
    let stratification = analyze_stratification(block);
    let size_estimate = estimate_block_size(block, config);
    let signature_analysis = analyze_signatures(block);
    Ok(MutualDeclExt3Result {
        cycles,
        elaboration_order,
        forward_ref_count,
        type_dependencies,
        stratification,
        size_estimate,
        signature_analysis,
    })
}

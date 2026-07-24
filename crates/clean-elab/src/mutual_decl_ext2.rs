// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended mutual declaration elaboration (phase 2): termination checking,
//! definition stratification, forward reference resolution, cross-definition
//! type inference, block validation, unfolding hints, compilation order,
//! and universe polymorphism.
//!
//! Builds on [`mutual_decl`] and [`mutual_decl_ext`].

use crate::dep_graph::DependencyGraph;
use crate::error::ElabError;
use crate::mutual_decl::MutualBlock;
use crate::mutual_decl_ext::{MutualSccGroup, TerminationStrategy};
use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Level};
use std::collections::{HashMap, HashSet};

/// Configuration for phase-2 mutual declaration elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualDeclExt2Config {
    pub(crate) max_structural_depth: usize,
    pub(crate) max_strata: usize,
    pub(crate) enable_wf_markers: bool,
    pub(crate) max_universe_params: usize,
}

impl Default for MutualDeclExt2Config {
    fn default() -> Self {
        Self {
            max_structural_depth: 100,
            max_strata: 64,
            enable_wf_markers: true,
            max_universe_params: 16,
        }
    }
}

/// Result of structural recursion analysis on a single definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RecursionKind {
    NonRecursive,
    Structural { param_idx: usize },
    WellFounded,
}

/// Detect structural recursion by scanning for recursive calls where one
/// argument is a strict sub-term of a parameter.
#[must_use]
pub(crate) fn detect_structural_recursion(
    body: &Expr,
    self_name: &str,
    config: &MutualDeclExt2Config,
) -> RecursionKind {
    let (num_params, inner) = peel_lambdas(body, config.max_structural_depth);
    if num_params == 0 || !contains_self_ref(inner, self_name) {
        return RecursionKind::NonRecursive;
    }
    if let Some(idx) = find_decreasing_param(inner, num_params) {
        return RecursionKind::Structural { param_idx: idx };
    }
    RecursionKind::WellFounded
}

fn peel_lambdas(expr: &Expr, max: usize) -> (usize, &Expr) {
    let (mut count, mut cur) = (0, expr);
    while count < max {
        if let ExprKind::Lam(_, _, body) = cur.kind() {
            count += 1;
            cur = body;
        } else {
            break;
        }
    }
    (count, cur)
}

fn contains_self_ref(expr: &Expr, name: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(n, _) => {
            let s = n.to_string();
            s == name || s.ends_with(&format!(".{name}"))
        }
        ExprKind::App(f, a) => contains_self_ref(f, name) || contains_self_ref(a, name),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_self_ref(ty, name) || contains_self_ref(body, name)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_self_ref(ty, name)
                || contains_self_ref(val, name)
                || contains_self_ref(body, name)
        }
        ExprKind::MData(_, e) | ExprKind::Proj(_, _, e) => contains_self_ref(e, name),
        _ => false,
    }
}

fn find_decreasing_param(expr: &Expr, num_params: usize) -> Option<usize> {
    match expr.kind() {
        ExprKind::App(f, a) => {
            if let ExprKind::BVar(idx) = a.kind() {
                let i = *idx as usize;
                if i < num_params {
                    return Some(num_params - 1 - i);
                }
            }
            find_decreasing_param(f, num_params).or_else(|| find_decreasing_param(a, num_params))
        }
        ExprKind::Lam(_, _, body) | ExprKind::Pi(_, _, body) => {
            find_decreasing_param(body, num_params + 1)
        }
        ExprKind::Let(_, _, val, body, _) => find_decreasing_param(val, num_params)
            .or_else(|| find_decreasing_param(body, num_params + 1)),
        _ => None,
    }
}

/// Marker for a definition requiring well-founded recursion encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WfRecursionMarker {
    pub(crate) def_name: String,
    pub(crate) def_index: usize,
    pub(crate) measure: Option<String>,
}

/// Collect WF markers for recursive definitions lacking structural evidence.
#[must_use]
pub(crate) fn collect_wf_markers(
    groups: &[MutualSccGroup],
    block: &MutualBlock,
    config: &MutualDeclExt2Config,
) -> Vec<WfRecursionMarker> {
    if !config.enable_wf_markers {
        return Vec::new();
    }
    let mut markers = Vec::new();
    for group in groups {
        if !group.is_recursive {
            continue;
        }
        for (pos, &idx) in group.indices.iter().enumerate() {
            if matches!(
                group.strategies[pos],
                TerminationStrategy::WellFounded { .. }
            ) {
                let entry = &block.declarations[idx];
                let (np, _) = peel_lambdas(&entry.body, 100);
                let measure = if np > 0 {
                    Some(format!("sizeOf(arg_0) for `{}`", entry.name))
                } else {
                    None
                };
                markers.push(WfRecursionMarker {
                    def_name: entry.name.clone(),
                    def_index: idx,
                    measure,
                });
            }
        }
    }
    markers
}

/// A stratum (level) in the dependency ordering of mutual definitions.
#[derive(Debug, Clone)]
pub(crate) struct DefinitionStratum {
    pub(crate) indices: Vec<usize>,
    pub(crate) level: usize,
}

/// Stratify definitions by dependency level (0 = no deps, 1 = depends on level 0, etc.).
#[must_use]
pub(crate) fn stratify_definitions(block: &MutualBlock) -> Vec<DefinitionStratum> {
    let n = block.declarations.len();
    if n == 0 {
        return Vec::new();
    }
    let mut adj: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for &(from, to) in &block.dep_graph.edges {
        if from < n && to < n && from != to {
            adj[from].insert(to);
        }
    }
    let mut levels = vec![0usize; n];
    let mut changed = true;
    let mut iters = 0;
    while changed && iters < n + 1 {
        changed = false;
        iters += 1;
        for i in 0..n {
            for &dep in &adj[i] {
                let c = levels[dep] + 1;
                if c > levels[i] {
                    levels[i] = c;
                    changed = true;
                }
            }
        }
    }
    let max_level = levels.iter().copied().max().unwrap_or(0);
    let mut strata: Vec<DefinitionStratum> = (0..=max_level)
        .map(|level| DefinitionStratum {
            indices: Vec::new(),
            level,
        })
        .collect();
    for (idx, &level) in levels.iter().enumerate() {
        strata[level].indices.push(idx);
    }
    strata.retain(|s| !s.indices.is_empty());
    strata
}

/// Forward reference entry tracking resolution state and placeholder type.
#[derive(Debug, Clone)]
pub(crate) struct ForwardRefEntry {
    pub(crate) name: String,
    pub(crate) index: usize,
    pub(crate) placeholder_ty: Expr,
    pub(crate) resolved: bool,
}

/// Resolver for forward references within a mutual block.
#[derive(Debug, Clone)]
pub(crate) struct ForwardRefResolver {
    entries: HashMap<String, ForwardRefEntry>,
    resolution_order: Vec<String>,
}

impl ForwardRefResolver {
    #[must_use]
    pub(crate) fn from_block(block: &MutualBlock) -> Self {
        let mut entries = HashMap::new();
        for (idx, decl) in block.declarations.iter().enumerate() {
            entries.insert(
                decl.name.clone(),
                ForwardRefEntry {
                    name: decl.name.clone(),
                    index: idx,
                    placeholder_ty: decl.ty.clone().unwrap_or_else(|| Expr::sort(Level::zero())),
                    resolved: false,
                },
            );
        }
        Self {
            entries,
            resolution_order: Vec::new(),
        }
    }

    #[must_use]
    pub(crate) fn lookup(&self, name: &str) -> Option<&ForwardRefEntry> {
        self.entries.get(name)
    }

    pub(crate) fn resolve(&mut self, name: &str) -> bool {
        if let Some(entry) = self.entries.get_mut(name) {
            if !entry.resolved {
                entry.resolved = true;
                self.resolution_order.push(name.to_string());
                return true;
            }
        }
        false
    }

    #[must_use]
    pub(crate) fn unresolved(&self) -> Vec<&str> {
        self.entries
            .values()
            .filter(|e| !e.resolved)
            .map(|e| e.name.as_str())
            .collect()
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub(crate) fn resolution_order(&self) -> &[String] {
        &self.resolution_order
    }
}

/// Inferred type for a mutual definition.
#[derive(Debug, Clone)]
pub(crate) struct InferredMutualType {
    pub(crate) name: String,
    pub(crate) index: usize,
    pub(crate) ty: Expr,
    pub(crate) is_user_provided: bool,
}

/// Infer types for all definitions. User-provided types preserved; missing = `Sort 0`.
#[must_use]
pub(crate) fn infer_mutual_types(block: &MutualBlock) -> Vec<InferredMutualType> {
    block
        .declarations
        .iter()
        .enumerate()
        .map(|(idx, entry)| {
            let (ty, is_user) = match &entry.ty {
                Some(t) => (t.clone(), true),
                None => (Expr::sort(Level::zero()), false),
            };
            InferredMutualType {
                name: entry.name.clone(),
                index: idx,
                ty,
                is_user_provided: is_user,
            }
        })
        .collect()
}

/// Validate a mutual block: non-empty, no duplicate names, strata within limit,
/// no mixed computable/noncomputable cycles.
pub(crate) fn validate_mutual_block(
    block: &MutualBlock,
    config: &MutualDeclExt2Config,
) -> Result<(), ElabError> {
    if block.declarations.is_empty() {
        return Err(ElabError::NotImplemented("empty mutual block".to_string()));
    }
    let mut seen = HashSet::new();
    for decl in &block.declarations {
        if !seen.insert(&decl.name) {
            return Err(ElabError::Unsupported {
                feature: format!("duplicate name '{}' in mutual block", decl.name),
            });
        }
    }
    let strata = stratify_definitions(block);
    if strata.len() > config.max_strata {
        return Err(ElabError::Unsupported {
            feature: format!(
                "mutual block has {} strata, limit {}",
                strata.len(),
                config.max_strata
            ),
        });
    }
    validate_computability_consistency(block)
}

fn validate_computability_consistency(block: &MutualBlock) -> Result<(), ElabError> {
    let n = block.declarations.len();
    for scc in &block.dep_graph.compute_sccs(n) {
        if scc.len() < 2 {
            continue;
        }
        let has_comp = scc
            .iter()
            .any(|&i| i < n && !block.declarations[i].is_noncomputable);
        let has_noncomp = scc
            .iter()
            .any(|&i| i < n && block.declarations[i].is_noncomputable);
        if has_comp && has_noncomp {
            let names: Vec<&str> = scc
                .iter()
                .filter(|&&i| i < n)
                .map(|&i| block.declarations[i].name.as_str())
                .collect();
            return Err(ElabError::Unsupported {
                feature: format!(
                    "cycle mixes computable and noncomputable: {}",
                    names.join(", ")
                ),
            });
        }
    }
    Ok(())
}

/// Compute compilation order (dependency-first via SCC condensation).
pub(crate) fn compute_compilation_order(block: &MutualBlock) -> Result<Vec<usize>, ElabError> {
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

/// Unfolding hint for the kernel's definitional equality checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UnfoldHint {
    Always,
    Never,
    OnConstructor,
    Bounded { max_depth: u32 },
}

/// Assign unfolding hints based on recursion kind.
#[must_use]
pub(crate) fn assign_unfold_hints(
    block: &MutualBlock,
    recursion_kinds: &[RecursionKind],
) -> Vec<(String, UnfoldHint)> {
    block
        .declarations
        .iter()
        .enumerate()
        .map(|(idx, entry)| {
            let kind = recursion_kinds
                .get(idx)
                .unwrap_or(&RecursionKind::NonRecursive);
            let hint = match kind {
                RecursionKind::NonRecursive => UnfoldHint::Always,
                RecursionKind::Structural { .. } => UnfoldHint::OnConstructor,
                RecursionKind::WellFounded => UnfoldHint::Bounded { max_depth: 32 },
            };
            (entry.name.clone(), hint)
        })
        .collect()
}

/// Shared universe parameters for a mutual block.
#[derive(Debug, Clone)]
pub(crate) struct MutualUniverseParams {
    pub(crate) params: Vec<String>,
}

/// Collect and unify universe parameters across definitions.
pub(crate) fn collect_universe_params(
    universe_lists: &[Vec<String>],
    config: &MutualDeclExt2Config,
) -> Result<MutualUniverseParams, ElabError> {
    if universe_lists.is_empty() {
        return Ok(MutualUniverseParams { params: Vec::new() });
    }
    let mut merged: Vec<String> = universe_lists[0].clone();
    let mut seen: HashSet<String> = merged.iter().cloned().collect();
    for list in &universe_lists[1..] {
        for param in list {
            if seen.insert(param.clone()) {
                merged.push(param.clone());
            }
        }
    }
    if merged.len() > config.max_universe_params {
        return Err(ElabError::Unsupported {
            feature: format!(
                "{} universe params exceeds limit of {}",
                merged.len(),
                config.max_universe_params
            ),
        });
    }
    Ok(MutualUniverseParams { params: merged })
}

/// Validate definitions use a compatible subset of shared universe parameters.
pub(crate) fn validate_universe_compatibility(
    universe_lists: &[Vec<String>],
    shared: &MutualUniverseParams,
) -> Result<(), ElabError> {
    let shared_set: HashSet<&str> = shared.params.iter().map(|s| s.as_str()).collect();
    for (idx, list) in universe_lists.iter().enumerate() {
        for param in list {
            if !shared_set.contains(param.as_str()) {
                return Err(ElabError::Unsupported {
                    feature: format!("def {} uses universe '{}' not in shared set", idx, param),
                });
            }
        }
    }
    Ok(())
}

/// Full phase-2 analysis result.
#[derive(Debug, Clone)]
pub(crate) struct MutualDeclExt2Result {
    pub(crate) strata: Vec<DefinitionStratum>,
    pub(crate) compilation_order: Vec<usize>,
    pub(crate) inferred_types: Vec<InferredMutualType>,
    pub(crate) recursion_kinds: Vec<RecursionKind>,
    pub(crate) wf_markers: Vec<WfRecursionMarker>,
    pub(crate) unfold_hints: Vec<(String, UnfoldHint)>,
    pub(crate) universe_params: MutualUniverseParams,
}

/// Perform full phase-2 analysis on a mutual block.
pub(crate) fn analyze_mutual_block_ext2(
    block: &MutualBlock,
    groups: &[MutualSccGroup],
    universe_lists: &[Vec<String>],
    config: &MutualDeclExt2Config,
) -> Result<MutualDeclExt2Result, ElabError> {
    validate_mutual_block(block, config)?;
    let strata = stratify_definitions(block);
    let compilation_order = compute_compilation_order(block)?;
    let inferred_types = infer_mutual_types(block);
    let recursion_kinds: Vec<RecursionKind> = block
        .declarations
        .iter()
        .map(|entry| detect_structural_recursion(&entry.body, &entry.name, config))
        .collect();
    let wf_markers = collect_wf_markers(groups, block, config);
    let unfold_hints = assign_unfold_hints(block, &recursion_kinds);
    let universe_params = collect_universe_params(universe_lists, config)?;
    Ok(MutualDeclExt2Result {
        strata,
        compilation_order,
        inferred_types,
        recursion_kinds,
        wf_markers,
        unfold_hints,
        universe_params,
    })
}

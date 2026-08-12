// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended mutual declaration elaboration: SCC analysis, type pre-elaboration,
//! termination metric inference, well-founded recursion encoding, forward
//! reference resolution, and controlled unfolding.
//!
//! Builds on [`mutual_decl`] for basic `mutual ... end` blocks.
//!
//! Lean 4 reference: `src/Lean/Elab/MutualDef.lean`.

use crate::dep_graph::DependencyGraph;
use crate::error::ElabError;
use crate::mutual_decl::MutualBlock;
use clean_kernel::{Expr, Level};
use clean_parser::{TerminationHints, TerminationKind};
use std::collections::HashMap;

/// Configuration for extended mutual declaration elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualDeclExtConfig {
    pub(crate) max_mutual_defs: usize,
    pub(crate) max_unfold_depth: u32,
    pub(crate) try_structural: bool,
    pub(crate) allow_wf_fallback: bool,
}

impl Default for MutualDeclExtConfig {
    fn default() -> Self {
        Self {
            max_mutual_defs: 64,
            max_unfold_depth: 32,
            try_structural: true,
            allow_wf_fallback: true,
        }
    }
}

/// A strongly connected component of mutual declarations.
#[derive(Debug, Clone)]
pub(crate) struct MutualSccGroup {
    /// Indices into the parent block's declaration list.
    pub(crate) indices: Vec<usize>,
    pub(crate) is_recursive: bool,
    /// Termination strategy per member (parallel to `indices`).
    pub(crate) strategies: Vec<TerminationStrategy>,
}

/// Termination strategy for a single declaration in a mutual group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TerminationStrategy {
    NonRecursive,
    Structural { decreasing_arg: usize },
    WellFounded { measure_desc: Option<String> },
    UserProvided { hint: String },
}

/// Partition a mutual block into SCC groups in topological order.
#[must_use]
pub(crate) fn partition_into_sccs(block: &MutualBlock) -> Vec<MutualSccGroup> {
    let n = block.declarations.len();
    if n == 0 {
        return Vec::new();
    }
    let sccs = block.dep_graph.compute_sccs(n);

    // Map nodes to their SCC index.
    let mut node_to_scc: Vec<usize> = vec![0; n];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &node in scc {
            if node < n {
                node_to_scc[node] = scc_idx;
            }
        }
    }

    // Build condensation graph and topologically sort SCCs.
    let num_sccs = sccs.len();
    let mut cond_graph = DependencyGraph::new();
    for &(from, to) in &block.dep_graph.edges {
        if from < n && to < n {
            let (sf, st) = (node_to_scc[from], node_to_scc[to]);
            if sf != st {
                cond_graph.add_edge(sf, st);
            }
        }
    }
    let order = cond_graph
        .topological_sort(num_sccs)
        .unwrap_or_else(|_| (0..num_sccs).collect());

    order
        .into_iter()
        .map(|scc_idx| {
            let mut indices: Vec<usize> =
                sccs[scc_idx].iter().copied().filter(|&i| i < n).collect();
            indices.sort_unstable();
            let is_recursive = if indices.len() > 1 {
                true
            } else if indices.len() == 1 {
                let idx = indices[0];
                block
                    .dep_graph
                    .edges
                    .iter()
                    .any(|&(f, t)| f == idx && t == idx)
            } else {
                false
            };
            let strategies = indices
                .iter()
                .map(|_| {
                    if is_recursive {
                        TerminationStrategy::WellFounded { measure_desc: None }
                    } else {
                        TerminationStrategy::NonRecursive
                    }
                })
                .collect();
            MutualSccGroup {
                indices,
                is_recursive,
                strategies,
            }
        })
        .collect()
}

/// Pre-elaborated type signature for a mutual declaration.
#[derive(Debug, Clone)]
pub(crate) struct PreElabSignature {
    pub(crate) name: String,
    pub(crate) index: usize,
    pub(crate) ty: Expr,
    pub(crate) num_params: usize,
}

/// Pre-elaborate type signatures (first pass before bodies).
#[must_use]
pub(crate) fn pre_elaborate_signatures(block: &MutualBlock) -> Vec<PreElabSignature> {
    block
        .declarations
        .iter()
        .enumerate()
        .map(|(idx, entry)| {
            let ty = entry
                .ty
                .clone()
                .unwrap_or_else(|| Expr::sort(Level::zero()));
            let num_params = count_pi_params(&ty);
            PreElabSignature {
                name: entry.name.clone(),
                index: idx,
                ty,
                num_params,
            }
        })
        .collect()
}

fn count_pi_params(expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = expr;
    while let clean_kernel::ExprKind::Pi(_, _, body) = current.kind() {
        count += 1;
        current = body;
    }
    count
}

/// Infer termination strategies for declarations in a recursive SCC group.
pub(crate) fn infer_termination_metrics(
    group: &mut MutualSccGroup,
    block: &MutualBlock,
    hints: &[Option<TerminationHints>],
    config: &MutualDeclExtConfig,
) {
    if !group.is_recursive {
        return;
    }
    for (pos, &idx) in group.indices.iter().enumerate() {
        if let Some(Some(hint)) = hints.get(idx) {
            if hint.termination_by.is_some() || hint.decreasing_by.is_some() {
                group.strategies[pos] = TerminationStrategy::UserProvided {
                    hint: format_termination_hint(hint),
                };
                continue;
            }
        }
        let entry = &block.declarations[idx];
        if config.try_structural {
            if let Some(dec_arg) = detect_structural_decrease_kernel(&entry.body) {
                group.strategies[pos] = TerminationStrategy::Structural {
                    decreasing_arg: dec_arg,
                };
                continue;
            }
        }
        if config.allow_wf_fallback {
            let measure = infer_wf_measure(&entry.body, &entry.name);
            group.strategies[pos] = TerminationStrategy::WellFounded {
                measure_desc: measure,
            };
        }
    }
}

fn format_termination_hint(hint: &TerminationHints) -> String {
    if let Some(ref tb) = hint.termination_by {
        match &tb.kind {
            TerminationKind::Structural(param) => format!("structural on {param}"),
            TerminationKind::WellFounded => {
                if tb.measure.is_some() {
                    "well_founded (measure provided)".into()
                } else {
                    "well_founded".into()
                }
            }
            TerminationKind::Query => "query".into(),
        }
    } else if hint.decreasing_by.is_some() {
        "decreasing_by (tactic)".into()
    } else {
        "unspecified".into()
    }
}

fn detect_structural_decrease_kernel(body: &Expr) -> Option<usize> {
    let mut params = 0usize;
    let mut current = body;
    while let clean_kernel::ExprKind::Lam(_, _, inner) = current.kind() {
        params += 1;
        current = inner;
    }
    if params == 0 {
        return None;
    }
    find_match_scrutinee_bvar(current, params)
}

fn find_match_scrutinee_bvar(expr: &Expr, num_params: usize) -> Option<usize> {
    match expr.kind() {
        clean_kernel::ExprKind::App(f, a) => {
            if let clean_kernel::ExprKind::BVar(idx) = a.kind() {
                let param_pos = num_params.checked_sub(1 + *idx as usize)?;
                if param_pos < num_params {
                    return Some(param_pos);
                }
            }
            find_match_scrutinee_bvar(f, num_params)
                .or_else(|| find_match_scrutinee_bvar(a, num_params))
        }
        clean_kernel::ExprKind::Let(_, _, val, body, _) => {
            find_match_scrutinee_bvar(val, num_params)
                .or_else(|| find_match_scrutinee_bvar(body, num_params + 1))
        }
        clean_kernel::ExprKind::Lam(_, _, body) | clean_kernel::ExprKind::Pi(_, _, body) => {
            find_match_scrutinee_bvar(body, num_params + 1)
        }
        _ => None,
    }
}

fn infer_wf_measure(body: &Expr, name: &str) -> Option<String> {
    let mut params = 0usize;
    let mut current = body;
    while let clean_kernel::ExprKind::Lam(_, _, inner) = current.kind() {
        params += 1;
        current = inner;
    }
    if params > 0 {
        Some(format!("sizeOf (arg 0) for {name}"))
    } else {
        None
    }
}

/// Encode a mutually recursive group via `WellFounded.fix` with sum-type packing.
pub(crate) fn encode_wf_mutual(
    group: &MutualSccGroup,
    block: &MutualBlock,
) -> Result<Vec<WfEncodedDef>, ElabError> {
    if !group.is_recursive {
        return Err(ElabError::NotImplemented(
            "wf encoding for non-recursive group".into(),
        ));
    }
    let mut results = Vec::with_capacity(group.indices.len());
    for (pos, &idx) in group.indices.iter().enumerate() {
        let entry = &block.declarations[idx];
        let ty = entry
            .ty
            .clone()
            .unwrap_or_else(|| Expr::sort(Level::zero()));
        results.push(WfEncodedDef {
            name: entry.name.clone(),
            original_index: idx,
            encoded_type: ty,
            encoded_body: Expr::app(Expr::const_str("WellFounded.fix"), entry.body.clone()),
            strategy: group.strategies[pos].clone(),
        });
    }
    Ok(results)
}

/// Result of well-founded encoding for a single declaration.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct WfEncodedDef {
    pub(crate) name: String,
    pub(crate) original_index: usize,
    pub(crate) encoded_type: Expr,
    pub(crate) encoded_body: Expr,
    pub(crate) strategy: TerminationStrategy,
}

/// Forward reference context for mutual block elaboration.
#[derive(Debug, Clone)]
pub(crate) struct ForwardRefContext {
    entries: HashMap<String, ForwardRef>,
}

/// A forward reference to a sibling declaration.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct ForwardRef {
    pub(crate) ty: Expr,
    pub(crate) index: usize,
    pub(crate) resolved: bool,
}

impl ForwardRefContext {
    #[must_use]
    pub(crate) fn from_signatures(sigs: &[PreElabSignature]) -> Self {
        let entries = sigs
            .iter()
            .map(|sig| {
                (
                    sig.name.clone(),
                    ForwardRef {
                        ty: sig.ty.clone(),
                        index: sig.index,
                        resolved: false,
                    },
                )
            })
            .collect();
        Self { entries }
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&ForwardRef> {
        self.entries.get(name)
    }

    pub(crate) fn mark_resolved(&mut self, name: &str) {
        if let Some(entry) = self.entries.get_mut(name) {
            entry.resolved = true;
        }
    }

    #[must_use]
    pub(crate) fn unresolved_names(&self) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|(_, v)| !v.resolved)
            .map(|(k, _)| k.as_str())
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
}

/// Unfolding state for controlled reduction within mutual blocks.
#[derive(Debug, Clone)]
pub(crate) struct UnfoldState {
    depths: HashMap<String, u32>,
    max_depth: u32,
}

impl UnfoldState {
    #[must_use]
    pub(crate) fn new(max_depth: u32) -> Self {
        Self {
            depths: HashMap::new(),
            max_depth,
        }
    }

    #[must_use]
    pub(crate) fn can_unfold(&self, name: &str) -> bool {
        self.depths.get(name).copied().unwrap_or(0) < self.max_depth
    }

    pub(crate) fn record_unfold(&mut self, name: &str) -> bool {
        let depth = self.depths.entry(name.to_string()).or_insert(0);
        if *depth < self.max_depth {
            *depth += 1;
            true
        } else {
            false
        }
    }

    pub(crate) fn reset(&mut self, name: &str) {
        self.depths.remove(name);
    }

    pub(crate) fn reset_all(&mut self) {
        self.depths.clear();
    }

    #[must_use]
    pub(crate) fn depth(&self, name: &str) -> u32 {
        self.depths.get(name).copied().unwrap_or(0)
    }
}

/// Extended mutual block analysis result.
#[derive(Debug, Clone)]
pub(crate) struct MutualDeclExtResult {
    pub(crate) groups: Vec<MutualSccGroup>,
    pub(crate) signatures: Vec<PreElabSignature>,
    pub(crate) forward_refs: ForwardRefContext,
}

/// Analyze a mutual block: partition into SCCs, pre-elaborate types,
/// infer termination metrics, and build forward reference context.
pub(crate) fn analyze_mutual_block(
    block: &MutualBlock,
    hints: &[Option<TerminationHints>],
    config: &MutualDeclExtConfig,
) -> Result<MutualDeclExtResult, ElabError> {
    if block.declarations.len() > config.max_mutual_defs {
        return Err(ElabError::Unsupported {
            feature: format!(
                "mutual block with {} definitions exceeds limit of {}",
                block.declarations.len(),
                config.max_mutual_defs
            ),
        });
    }
    let signatures = pre_elaborate_signatures(block);
    let mut groups = partition_into_sccs(block);
    for group in &mut groups {
        infer_termination_metrics(group, block, hints, config);
    }
    let forward_refs = ForwardRefContext::from_signatures(&signatures);
    Ok(MutualDeclExtResult {
        groups,
        signatures,
        forward_refs,
    })
}

/// Validate SCC structure: reject mixed computable/noncomputable cycles
/// and unresolved termination strategies when wf fallback is disabled.
pub(crate) fn validate_scc_structure(
    result: &MutualDeclExtResult,
    block: &MutualBlock,
    config: &MutualDeclExtConfig,
) -> Result<(), ElabError> {
    for group in &result.groups {
        if !group.is_recursive {
            continue;
        }
        let has_comp = group
            .indices
            .iter()
            .any(|&i| !block.declarations[i].is_noncomputable);
        let has_noncomp = group
            .indices
            .iter()
            .any(|&i| block.declarations[i].is_noncomputable);
        if has_comp && has_noncomp {
            let names: Vec<&str> = group
                .indices
                .iter()
                .map(|&i| block.declarations[i].name.as_str())
                .collect();
            return Err(ElabError::Unsupported {
                feature: format!(
                    "recursive SCC mixes computable and noncomputable: {}",
                    names.join(", ")
                ),
            });
        }
        if !config.allow_wf_fallback {
            for (pos, strategy) in group.strategies.iter().enumerate() {
                if matches!(strategy, TerminationStrategy::WellFounded { .. }) {
                    let idx = group.indices[pos];
                    return Err(ElabError::Unsupported {
                        feature: format!(
                            "no structural recursion detected for '{}' and well-founded fallback is disabled",
                            block.declarations[idx].name
                        ),
                    });
                }
            }
        }
    }
    Ok(())
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended let-rec analysis (phase 2): mutual recursion classification,
//! termination hints, dependency ordering, recursion depth estimation,
//! binding statistics, inlining candidates, and well-foundedness hints.

use crate::let_rec_ext::LetRecBinding;
use clean_kernel::{Expr, ExprKind};
use std::collections::{HashMap, HashSet, VecDeque};
use thiserror::Error;

// =============================================================================
// Error type
// =============================================================================

#[derive(Debug, Clone, Error)]
pub(crate) enum LetRecExt2Error {
    #[error("empty binding set")]
    EmptyBindings,
    #[error("binding index {idx} out of range (max {max})")]
    IndexOutOfRange { idx: usize, max: usize },
    #[error("cycle detected in dependency graph involving {count} bindings")]
    CycleDetected { count: usize },
}

// =============================================================================
// Mutual recursion analysis
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MutualPattern {
    Independent,
    SelfRecursive,
    MutualRecursive,
    Leaf,
}

#[derive(Debug, Clone)]
pub(crate) struct MutualAnalysis {
    pub(crate) patterns: Vec<MutualPattern>,
    pub(crate) sccs: Vec<Vec<usize>>,
    pub(crate) forward_edges: Vec<HashSet<usize>>,
    pub(crate) reverse_edges: Vec<HashSet<usize>>,
}

/// Analyze mutual recursion patterns across a binding block.
pub(crate) fn analyze_mutual_recursion(
    bindings: &[LetRecBinding],
) -> Result<MutualAnalysis, LetRecExt2Error> {
    if bindings.is_empty() {
        return Err(LetRecExt2Error::EmptyBindings);
    }
    let n = bindings.len();
    let id_to_idx: HashMap<u64, usize> = bindings
        .iter()
        .enumerate()
        .map(|(i, b)| (b.fvar_id, i))
        .collect();
    let mut forward_edges: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    let mut reverse_edges: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (i, binding) in bindings.iter().enumerate() {
        let mut fvars = HashSet::new();
        collect_fvar_ids(&binding.body, &mut fvars);
        for fvar in &fvars {
            if let Some(&j) = id_to_idx.get(fvar) {
                forward_edges[i].insert(j);
                reverse_edges[j].insert(i);
            }
        }
    }
    let sccs = tarjan_scc(&forward_edges);
    let patterns = (0..n)
        .map(|i| classify_binding(i, &forward_edges, &reverse_edges, &sccs))
        .collect();
    Ok(MutualAnalysis {
        patterns,
        sccs,
        forward_edges,
        reverse_edges,
    })
}

fn classify_binding(
    idx: usize,
    forward: &[HashSet<usize>],
    reverse: &[HashSet<usize>],
    sccs: &[Vec<usize>],
) -> MutualPattern {
    let in_mutual_scc = sccs.iter().any(|scc| scc.len() > 1 && scc.contains(&idx));
    if in_mutual_scc {
        MutualPattern::MutualRecursive
    } else if forward[idx].contains(&idx) {
        MutualPattern::SelfRecursive
    } else if reverse[idx].iter().any(|&j| j != idx) && !forward[idx].iter().any(|&j| j != idx) {
        MutualPattern::Leaf
    } else {
        MutualPattern::Independent
    }
}

// =============================================================================
// Termination hints
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TerminationHint {
    pub(crate) decreasing_param: usize,
    pub(crate) param_name: String,
    pub(crate) evidence: DecreaseEvidence,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DecreaseEvidence {
    SubExprArg,
    DestructorApp { destructor: String },
    PatternMatch,
    InductiveType { type_name: String },
}

/// Collect termination hints for a binding by inspecting recursive call sites.
pub(crate) fn collect_termination_hints(binding: &LetRecBinding) -> Vec<TerminationHint> {
    let mut hints = Vec::new();
    let mut call_args: Vec<Vec<Expr>> = Vec::new();
    collect_recursive_call_args(&binding.body, binding.fvar_id, &mut call_args);
    if call_args.is_empty() {
        return hints;
    }
    for (pi, (pname, pty)) in binding.params.iter().enumerate() {
        if let Some(tn) = inductive_type_name(pty) {
            hints.push(TerminationHint {
                decreasing_param: pi,
                param_name: pname.clone(),
                evidence: DecreaseEvidence::InductiveType { type_name: tn },
            });
        }
        let bvar_idx = binding.params.len().saturating_sub(pi + 1) as u32;
        for args in &call_args {
            if let Some(arg) = args.get(pi) {
                if !matches!(arg.kind(), ExprKind::BVar(idx) if *idx == bvar_idx) {
                    if let Some(destr) = extract_destructor(arg) {
                        if !hints.iter().any(|h| h.decreasing_param == pi && matches!(&h.evidence, DecreaseEvidence::DestructorApp { destructor } if destructor == &destr)) {
                            hints.push(TerminationHint { decreasing_param: pi, param_name: pname.clone(), evidence: DecreaseEvidence::DestructorApp { destructor: destr } });
                        }
                    } else if !hints.iter().any(|h| {
                        h.decreasing_param == pi && h.evidence == DecreaseEvidence::SubExprArg
                    }) {
                        hints.push(TerminationHint {
                            decreasing_param: pi,
                            param_name: pname.clone(),
                            evidence: DecreaseEvidence::SubExprArg,
                        });
                    }
                }
            }
        }
    }
    hints
}

// =============================================================================
// Dependency ordering (topological sort, Kahn's algorithm)
// =============================================================================

pub(crate) fn dependency_order(bindings: &[LetRecBinding]) -> Result<Vec<usize>, LetRecExt2Error> {
    if bindings.is_empty() {
        return Err(LetRecExt2Error::EmptyBindings);
    }
    let n = bindings.len();
    let id_to_idx: HashMap<u64, usize> = bindings
        .iter()
        .enumerate()
        .map(|(i, b)| (b.fvar_id, i))
        .collect();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut in_degree = vec![0usize; n];
    for (i, binding) in bindings.iter().enumerate() {
        let mut fvars = HashSet::new();
        collect_fvar_ids(&binding.body, &mut fvars);
        for fvar in &fvars {
            if let Some(&j) = id_to_idx.get(fvar) {
                if i != j {
                    adj[j].push(i);
                    in_degree[i] += 1;
                }
            }
        }
    }
    let mut queue: VecDeque<usize> = in_degree
        .iter()
        .enumerate()
        .filter_map(|(i, &d)| (d == 0).then_some(i))
        .collect();
    let mut order = Vec::with_capacity(n);
    while let Some(node) = queue.pop_front() {
        order.push(node);
        for &dep in &adj[node] {
            in_degree[dep] -= 1;
            if in_degree[dep] == 0 {
                queue.push_back(dep);
            }
        }
    }
    if order.len() == n {
        Ok(order)
    } else {
        Err(LetRecExt2Error::CycleDetected {
            count: n - order.len(),
        })
    }
}

// =============================================================================
// Recursion depth estimation
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DepthEstimate {
    pub(crate) call_site_count: usize,
    pub(crate) max_call_nesting: usize,
    pub(crate) has_tail_calls: bool,
    pub(crate) is_nonlinear: bool,
}

pub(crate) fn estimate_recursion_depth(binding: &LetRecBinding) -> DepthEstimate {
    let mut call_args: Vec<Vec<Expr>> = Vec::new();
    collect_recursive_call_args(&binding.body, binding.fvar_id, &mut call_args);
    DepthEstimate {
        call_site_count: call_args.len(),
        max_call_nesting: max_nesting_depth(&binding.body, binding.fvar_id, 0),
        has_tail_calls: is_tail_position_call(&binding.body, binding.fvar_id),
        is_nonlinear: count_calls_in_branch(&binding.body, binding.fvar_id) > 1,
    }
}

// =============================================================================
// Binding statistics
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BindingStats {
    pub(crate) total: usize,
    pub(crate) self_recursive: usize,
    pub(crate) mutual_recursive: usize,
    pub(crate) non_recursive: usize,
    pub(crate) leaf: usize,
    pub(crate) total_expr_size: usize,
    pub(crate) max_expr_size: usize,
    pub(crate) total_params: usize,
}

pub(crate) fn compute_binding_stats(
    bindings: &[LetRecBinding],
) -> Result<BindingStats, LetRecExt2Error> {
    if bindings.is_empty() {
        return Err(LetRecExt2Error::EmptyBindings);
    }
    let analysis = analyze_mutual_recursion(bindings)?;
    let mut stats = BindingStats {
        total: bindings.len(),
        self_recursive: 0,
        mutual_recursive: 0,
        non_recursive: 0,
        leaf: 0,
        total_expr_size: 0,
        max_expr_size: 0,
        total_params: 0,
    };
    for (i, binding) in bindings.iter().enumerate() {
        match analysis.patterns[i] {
            MutualPattern::SelfRecursive => stats.self_recursive += 1,
            MutualPattern::MutualRecursive => stats.mutual_recursive += 1,
            MutualPattern::Independent => stats.non_recursive += 1,
            MutualPattern::Leaf => stats.leaf += 1,
        }
        let size = expr_size(&binding.body);
        stats.total_expr_size += size;
        stats.max_expr_size = stats.max_expr_size.max(size);
        stats.total_params += binding.params.len();
    }
    Ok(stats)
}

// =============================================================================
// Inlining candidates
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct InliningCandidate {
    pub(crate) binding_idx: usize,
    pub(crate) name: String,
    pub(crate) score: f64,
    pub(crate) reasons: Vec<InliningReason>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InliningReason {
    SmallBody { size: usize },
    NonRecursive,
    SingleUse,
    LeafBinding,
    LargeBody { size: usize },
    Recursive,
    MutualRecursion,
}

pub(crate) fn score_inlining_candidates(
    bindings: &[LetRecBinding],
) -> Result<Vec<InliningCandidate>, LetRecExt2Error> {
    if bindings.is_empty() {
        return Err(LetRecExt2Error::EmptyBindings);
    }
    let analysis = analyze_mutual_recursion(bindings)?;
    let id_to_idx: HashMap<u64, usize> = bindings
        .iter()
        .enumerate()
        .map(|(i, b)| (b.fvar_id, i))
        .collect();
    let mut use_counts = vec![0usize; bindings.len()];
    for binding in bindings {
        let mut fvars = HashSet::new();
        collect_fvar_ids(&binding.body, &mut fvars);
        for fvar in &fvars {
            if let Some(&idx) = id_to_idx.get(fvar) {
                use_counts[idx] += 1;
            }
        }
    }
    Ok(bindings
        .iter()
        .enumerate()
        .map(|(i, binding)| {
            let size = expr_size(&binding.body);
            let mut score: f64 = 0.5;
            let mut reasons = Vec::new();
            if size <= 10 {
                score += 0.3;
                reasons.push(InliningReason::SmallBody { size });
            } else if size > 50 {
                score -= 0.3;
                reasons.push(InliningReason::LargeBody { size });
            }
            match analysis.patterns[i] {
                MutualPattern::Independent => {
                    score += 0.2;
                    reasons.push(InliningReason::NonRecursive);
                }
                MutualPattern::Leaf => {
                    score += 0.15;
                    reasons.push(InliningReason::LeafBinding);
                }
                MutualPattern::SelfRecursive => {
                    // Wave 101: deepen the penalty so a small (size <= 10)
                    // self-recursive body lands strictly below 0.5 even with
                    // the single-use bonus. Threshold derivation:
                    //   0.5 (base) + 0.3 (SmallBody) - X + 0.1 (SingleUse)
                    //     < 0.5  ==>  X > 0.4. Pick X = 0.5.
                    score -= 0.5;
                    reasons.push(InliningReason::Recursive);
                }
                MutualPattern::MutualRecursive => {
                    // Wave 101: deepen the penalty so a small (size <= 10)
                    // mutually-recursive body lands strictly below 0.3 even
                    // with the single-use bonus. Threshold derivation:
                    //   0.5 (base) + 0.3 (SmallBody) - X + 0.1 (SingleUse)
                    //     < 0.3  ==>  X > 0.6. Pick X = 0.7.
                    score -= 0.7;
                    reasons.push(InliningReason::MutualRecursion);
                }
            }
            if use_counts[i] <= 1 {
                score += 0.1;
                reasons.push(InliningReason::SingleUse);
            }
            InliningCandidate {
                binding_idx: i,
                name: binding.name.clone(),
                score: f64::clamp(score, 0.0, 1.0),
                reasons,
            }
        })
        .collect())
}

// =============================================================================
// Well-foundedness hints
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WellFoundednessHint {
    pub(crate) binding_idx: usize,
    pub(crate) relation: String,
    pub(crate) param_idx: usize,
    pub(crate) confidence: HintConfidence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HintConfidence {
    High,
    Medium,
    Low,
}

pub(crate) fn suggest_well_foundedness(
    bindings: &[LetRecBinding],
) -> Result<Vec<WellFoundednessHint>, LetRecExt2Error> {
    if bindings.is_empty() {
        return Err(LetRecExt2Error::EmptyBindings);
    }
    let mut hints = Vec::new();
    for (i, binding) in bindings.iter().enumerate() {
        let th = collect_termination_hints(binding);
        for t in &th {
            let (relation, confidence) = match &t.evidence {
                DecreaseEvidence::InductiveType { type_name } => {
                    let rel = match type_name.as_str() {
                        "Nat" => "Nat.lt",
                        "List" => "List.length",
                        "Fin" => "Fin.val",
                        _ => "",
                    };
                    if rel.is_empty() {
                        (format!("sizeOf (α := {type_name})"), HintConfidence::High)
                    } else {
                        (rel.to_string(), HintConfidence::High)
                    }
                }
                DecreaseEvidence::DestructorApp { destructor } => {
                    (format!("measure via {destructor}"), HintConfidence::Medium)
                }
                DecreaseEvidence::SubExprArg => ("sizeOf".to_string(), HintConfidence::Low),
                DecreaseEvidence::PatternMatch => {
                    ("structural".to_string(), HintConfidence::Medium)
                }
            };
            hints.push(WellFoundednessHint {
                binding_idx: i,
                relation,
                param_idx: t.decreasing_param,
                confidence,
            });
        }
        if th.is_empty() && mentions_fvar(&binding.body, binding.fvar_id) {
            for (pi, (_, pty)) in binding.params.iter().enumerate() {
                if !matches!(pty.kind(), ExprKind::Sort(_)) {
                    hints.push(WellFoundednessHint {
                        binding_idx: i,
                        relation: "sizeOf".to_string(),
                        param_idx: pi,
                        confidence: HintConfidence::Low,
                    });
                    break;
                }
            }
        }
    }
    Ok(hints)
}

// =============================================================================
// Internal helpers
// =============================================================================

fn collect_fvar_ids(expr: &Expr, out: &mut HashSet<u64>) {
    match expr.kind() {
        ExprKind::FVar(id) => {
            out.insert(id.as_u64());
        }
        ExprKind::App(f, a) => {
            collect_fvar_ids(f, out);
            collect_fvar_ids(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_fvar_ids(ty, out);
            collect_fvar_ids(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_fvar_ids(ty, out);
            collect_fvar_ids(val, out);
            collect_fvar_ids(body, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => collect_fvar_ids(inner, out),
        _ => {}
    }
}

fn mentions_fvar(expr: &Expr, target: u64) -> bool {
    let mut fvars = HashSet::new();
    collect_fvar_ids(expr, &mut fvars);
    fvars.contains(&target)
}

fn collect_recursive_call_args(expr: &Expr, target: u64, out: &mut Vec<Vec<Expr>>) {
    if let Some((head, args)) = app_spine(expr) {
        if matches!(head.kind(), ExprKind::FVar(id) if id.as_u64() == target) {
            out.push(args.into_iter().cloned().collect());
        }
    }
    match expr.kind() {
        ExprKind::App(f, a) => {
            collect_recursive_call_args(f, target, out);
            collect_recursive_call_args(a, target, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_recursive_call_args(ty, target, out);
            collect_recursive_call_args(body, target, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_recursive_call_args(ty, target, out);
            collect_recursive_call_args(val, target, out);
            collect_recursive_call_args(body, target, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            collect_recursive_call_args(inner, target, out)
        }
        _ => {}
    }
}

fn app_spine(expr: &Expr) -> Option<(&Expr, Vec<&Expr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App(f, a) = current.kind() {
        args.push(a.as_ref());
        current = f;
    }
    if args.is_empty() {
        None
    } else {
        args.reverse();
        Some((current, args))
    }
}

fn inductive_type_name(expr: &Expr) -> Option<String> {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            matches!(
                s.as_str(),
                "Nat" | "Bool" | "List" | "Option" | "Fin" | "Vector" | "Array" | "String" | "Int"
            )
            .then_some(s)
        }
        ExprKind::App(f, _) => inductive_type_name(f),
        _ => None,
    }
}

fn extract_destructor(expr: &Expr) -> Option<String> {
    let (head, _) = app_spine(expr)?;
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        if matches!(
            s.as_str(),
            "Nat.pred"
                | "Nat.sub"
                | "List.tail"
                | "List.head?"
                | "List.drop"
                | "Option.get!"
                | "Fin.val"
                | "String.drop"
        ) {
            return Some(s);
        }
    }
    None
}

fn expr_size(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::App(f, a) => 1 + expr_size(f) + expr_size(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            1 + expr_size(ty) + expr_size(body)
        }
        ExprKind::Let(_, ty, val, body, _) => 1 + expr_size(ty) + expr_size(val) + expr_size(body),
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => 1 + expr_size(inner),
        _ => 1,
    }
}

fn max_nesting_depth(expr: &Expr, target: u64, depth: usize) -> usize {
    if let Some((head, args)) = app_spine(expr) {
        if matches!(head.kind(), ExprKind::FVar(id) if id.as_u64() == target) {
            return args
                .iter()
                .map(|a| max_nesting_depth(a, target, depth + 1))
                .max()
                .unwrap_or(depth + 1);
        }
    }
    match expr.kind() {
        ExprKind::App(f, a) => {
            max_nesting_depth(f, target, depth).max(max_nesting_depth(a, target, depth))
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            max_nesting_depth(ty, target, depth).max(max_nesting_depth(body, target, depth))
        }
        ExprKind::Let(_, ty, val, body, _) => max_nesting_depth(ty, target, depth)
            .max(max_nesting_depth(val, target, depth))
            .max(max_nesting_depth(body, target, depth)),
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            max_nesting_depth(inner, target, depth)
        }
        _ => depth,
    }
}

fn is_tail_position_call(expr: &Expr, target: u64) -> bool {
    match expr.kind() {
        ExprKind::App(f, _) => {
            let mut head = f.as_ref();
            while let ExprKind::App(inner_f, _) = head.kind() {
                head = inner_f;
            }
            matches!(head.kind(), ExprKind::FVar(id) if id.as_u64() == target)
        }
        ExprKind::Let(_, _, _, body, _) | ExprKind::Lam(_, _, body) => {
            is_tail_position_call(body, target)
        }
        _ => false,
    }
}

fn count_calls_in_branch(expr: &Expr, target: u64) -> usize {
    // Wave 101: a recursive call at the application spine head counts as ONE
    // call, but we must still descend into the call's arguments because they
    // may contain *additional* recursive calls (e.g. `f(x) + f(x)` lowers to
    // `App(App(FVar(f), BVar(x)), App(FVar(f), BVar(x)))` — the outer spine
    // head is `f` applied to two args, the second of which is itself a call
    // to `f`). The previous implementation short-circuited at the first
    // spine match and dropped any nested calls in the args, so two calls in
    // the same branch were under-counted as one.
    if let Some((head, args)) = app_spine(expr) {
        if matches!(head.kind(), ExprKind::FVar(id) if id.as_u64() == target) {
            let arg_calls: usize = args.iter().map(|a| count_calls_in_branch(a, target)).sum();
            return 1 + arg_calls;
        }
    }
    match expr.kind() {
        ExprKind::App(f, a) => count_calls_in_branch(f, target) + count_calls_in_branch(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_calls_in_branch(ty, target) + count_calls_in_branch(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_calls_in_branch(ty, target)
                + count_calls_in_branch(val, target)
                + count_calls_in_branch(body, target)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            count_calls_in_branch(inner, target)
        }
        _ => 0,
    }
}

/// Tarjan's SCC algorithm. Returns SCCs sorted largest first.
fn tarjan_scc(adj: &[HashSet<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut idx_counter = 0u32;
    let mut stack = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![u32::MAX; n];
    let mut lowlinks = vec![u32::MAX; n];
    let mut sccs = Vec::new();
    fn sc(
        v: usize,
        adj: &[HashSet<usize>],
        ic: &mut u32,
        stack: &mut Vec<usize>,
        os: &mut [bool],
        ix: &mut [u32],
        ll: &mut [u32],
        out: &mut Vec<Vec<usize>>,
    ) {
        ix[v] = *ic;
        ll[v] = *ic;
        *ic += 1;
        stack.push(v);
        os[v] = true;
        for &w in &adj[v] {
            if ix[w] == u32::MAX {
                sc(w, adj, ic, stack, os, ix, ll, out);
                ll[v] = ll[v].min(ll[w]);
            } else if os[w] {
                ll[v] = ll[v].min(ix[w]);
            }
        }
        if ll[v] == ix[v] {
            let mut scc = Vec::new();
            while let Some(w) = stack.pop() {
                os[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            out.push(scc);
        }
    }
    for v in 0..n {
        if indices[v] == u32::MAX {
            sc(
                v,
                adj,
                &mut idx_counter,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut sccs,
            );
        }
    }
    sccs.sort_by_key(|b| std::cmp::Reverse(b.len()));
    sccs
}

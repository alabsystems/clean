// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended let-rec elaboration with mutual recursion, termination metrics, WF recursion, type inference, capture analysis, unfolding equations, partial function support, and nested let-rec flattening.

use clean_kernel::expr::BinderInfo;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Debug, Clone)]
pub(crate) struct LetRecExtConfig {
    pub(crate) max_mutual_depth: usize,
    pub(crate) enable_wf_fallback: bool,
    pub(crate) enable_type_inference: bool,
    pub(crate) enable_capture_analysis: bool,
    pub(crate) max_unfolding_depth: usize,
    pub(crate) allow_partial_functions: bool,
}
impl Default for LetRecExtConfig {
    fn default() -> Self {
        Self {
            max_mutual_depth: 16,
            enable_wf_fallback: true,
            enable_type_inference: true,
            enable_capture_analysis: true,
            max_unfolding_depth: 32,
            allow_partial_functions: false,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum TerminationMetric {
    Structural {
        decreasing_arg: usize,
        inductive_type: String,
    },
    WellFounded {
        measure: Expr,
        relation: Expr,
    },
    Unguarded,
}

#[derive(Debug, Clone)]
pub(crate) struct LetRecBinding {
    pub(crate) name: String,
    pub(crate) params: Vec<(String, Expr)>,
    pub(crate) return_type: Option<Expr>,
    pub(crate) body: Expr,
    pub(crate) fvar_id: u64,
}

#[derive(Debug, Clone)]
pub(crate) struct MutualBlock {
    pub(crate) bindings: Vec<LetRecBinding>,
    pub(crate) dep_graph: Vec<Vec<usize>>,
    pub(crate) metrics: Vec<TerminationMetric>,
}

#[derive(Debug, Clone)]
pub(crate) struct CaptureInfo {
    pub(crate) binding_idx: usize,
    pub(crate) captured_names: Vec<String>,
    pub(crate) captured_fvars: Vec<u64>,
}
#[derive(Debug, Clone)]
pub(crate) struct UnfoldingEquation {
    pub(crate) name: String,
    pub(crate) lhs: Expr,
    pub(crate) rhs: Expr,
    pub(crate) is_simp: bool,
}
#[derive(Debug, Clone)]
pub(crate) struct PartialFnInfo {
    pub(crate) name: String,
    pub(crate) missing_cases: Vec<Expr>,
    pub(crate) default_value: Option<Expr>,
}

#[derive(Debug, Clone, Error)]
pub(crate) enum LetRecExtError {
    #[error("mutual recursion depth {depth} exceeds max {max}")]
    MutualRecursionTooDeep { depth: usize, max: usize },
    #[error("termination check failed for {name}: {reason}")]
    TerminationCheckFailed { name: String, reason: String },
    #[error("type inference failed for {binding}: {msg}")]
    TypeInferenceFailed { binding: String, msg: String },
    #[error("cyclic dependency detected: {names:?}")]
    CyclicDependency { names: Vec<String> },
    #[error("partial function not allowed: {name}")]
    PartialFunctionNotAllowed { name: String },
    #[error("nested let-rec flattening failed: {reason}")]
    NestedFlattenFailed { reason: String },
}

pub(crate) fn build_mutual_block(
    bindings: &[(String, Vec<(String, Expr)>, Option<Expr>, Expr)],
    config: &LetRecExtConfig,
) -> Result<MutualBlock, LetRecExtError> {
    if bindings.len() > config.max_mutual_depth {
        return Err(LetRecExtError::MutualRecursionTooDeep {
            depth: bindings.len(),
            max: config.max_mutual_depth,
        });
    }
    let mut block_bindings = Vec::with_capacity(bindings.len());
    for (idx, (name, params, return_type, body)) in bindings.iter().enumerate() {
        let mut binding = LetRecBinding {
            name: name.clone(),
            params: params.clone(),
            return_type: return_type.clone(),
            body: body.clone(),
            fvar_id: idx as u64 + 1,
        };
        if binding.return_type.is_none() {
            if config.enable_type_inference {
                binding.return_type = infer_return_type(&binding);
            } else {
                return Err(LetRecExtError::TypeInferenceFailed {
                    binding: binding.name.clone(),
                    msg: "missing return type and inference is disabled".into(),
                });
            }
        }
        block_bindings.push(binding);
    }
    let dep_graph = compute_dep_graph(&block_bindings);
    let mut metrics = Vec::with_capacity(block_bindings.len());
    for binding in &block_bindings {
        let metric = detect_termination_metric(binding, &block_bindings);
        if matches!(metric, TerminationMetric::WellFounded { .. }) && !config.enable_wf_fallback {
            return Err(LetRecExtError::TerminationCheckFailed {
                name: binding.name.clone(),
                reason: "well-founded fallback is disabled".into(),
            });
        }
        metrics.push(metric);
    }
    let block = MutualBlock {
        bindings: block_bindings,
        dep_graph,
        metrics,
    };
    if config.enable_capture_analysis {
        let _ = analyze_captures(&block);
    }
    let _ = check_partial_functions(&block, config)?;
    Ok(block)
}

pub(crate) fn compute_dep_graph(bindings: &[LetRecBinding]) -> Vec<Vec<usize>> {
    bindings
        .iter()
        .enumerate()
        .map(|(idx, binding)| {
            let mut fvars = HashSet::new();
            collect_fvars(&binding.body, &mut fvars);
            bindings
                .iter()
                .enumerate()
                .filter_map(|(dep_idx, dep)| {
                    (idx != dep_idx && fvars.contains(&dep.fvar_id)).then_some(dep_idx)
                })
                .collect()
        })
        .collect()
}

pub(crate) fn detect_termination_metric(
    binding: &LetRecBinding,
    _all_bindings: &[LetRecBinding],
) -> TerminationMetric {
    if !mentions_fvar(&binding.body, binding.fvar_id) {
        return TerminationMetric::Unguarded;
    }
    let mut calls = Vec::new();
    collect_recursive_calls(&binding.body, binding.fvar_id, &mut calls);
    for (arg_idx, (_, ty)) in binding.params.iter().enumerate() {
        let direct_idx = binding.params.len().saturating_sub(arg_idx + 1) as u32;
        if calls.iter().any(|args| {
            args.get(arg_idx)
                .is_some_and(|arg| !matches!(arg.kind(), ExprKind::BVar(idx) if *idx == direct_idx))
        }) {
            return TerminationMetric::Structural {
                decreasing_arg: arg_idx,
                inductive_type: inductive_type_name(ty).unwrap_or_else(|| "Nat".into()),
            };
        }
    }
    TerminationMetric::WellFounded {
        measure: wf_placeholder_measure(),
        relation: wf_placeholder_relation(),
    }
}

fn wf_placeholder_measure() -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), Expr::const_str("Nat.zero"))
}

fn wf_placeholder_relation() -> Expr {
    Expr::app(Expr::const_str("WellFounded.placeholderRel"), Expr::type_())
}

pub(crate) fn infer_return_type(binding: &LetRecBinding) -> Option<Expr> {
    binding.return_type.clone().or_else(|| {
        Some(match binding.body.kind() {
            ExprKind::Sort(level) => Expr::sort(level.clone()),
            ExprKind::Const(name, _) => Expr::const_str(&name.to_string()),
            ExprKind::Lit(clean_kernel::Literal::Nat(_)) => Expr::const_str("Nat"),
            _ => Expr::type_(),
        })
    })
}

pub(crate) fn analyze_captures(block: &MutualBlock) -> Vec<CaptureInfo> {
    let local_ids: HashSet<u64> = block
        .bindings
        .iter()
        .map(|binding| binding.fvar_id)
        .collect();
    block
        .bindings
        .iter()
        .enumerate()
        .map(|(binding_idx, binding)| {
            let mut captured_fvars: Vec<u64> = {
                let mut found = HashSet::new();
                collect_fvars(&binding.body, &mut found);
                found
                    .into_iter()
                    .filter(|id| !local_ids.contains(id))
                    .collect()
            };
            captured_fvars.sort_unstable();
            CaptureInfo {
                binding_idx,
                captured_names: captured_fvars
                    .iter()
                    .map(|id| format!("fvar#{id}"))
                    .collect(),
                captured_fvars,
            }
        })
        .collect()
}

pub(crate) fn generate_unfolding_equations(block: &MutualBlock) -> Vec<UnfoldingEquation> {
    block
        .bindings
        .iter()
        .map(|binding| {
            let args: Vec<Expr> = binding
                .params
                .iter()
                .map(|(name, _)| Expr::const_str(name))
                .collect();
            let lhs = args.iter().fold(Expr::const_str(&binding.name), |f, arg| {
                Expr::app(f, arg.clone())
            });
            let rhs = if binding.body.has_loose_bvars_quick() {
                binding.body.instantiate_rev(&args)
            } else {
                binding.body.clone()
            };
            UnfoldingEquation {
                name: binding.name.clone(),
                lhs,
                rhs,
                is_simp: !mentions_fvar(&binding.body, binding.fvar_id),
            }
        })
        .collect()
}

pub(crate) fn check_partial_functions(
    block: &MutualBlock,
    config: &LetRecExtConfig,
) -> Result<Vec<PartialFnInfo>, LetRecExtError> {
    let infos: Vec<PartialFnInfo> = block
        .bindings
        .iter()
        .filter_map(|binding| {
            find_partial_marker(&binding.body).map(|marker| PartialFnInfo {
                name: binding.name.clone(),
                missing_cases: vec![marker],
                default_value: contains_const(&binding.body, "Inhabited.default")
                    .then(|| Expr::const_str("Inhabited.default")),
            })
        })
        .collect();
    if !config.allow_partial_functions {
        if let Some(info) = infos.first() {
            return Err(LetRecExtError::PartialFunctionNotAllowed {
                name: info.name.clone(),
            });
        }
    }
    Ok(infos)
}

pub(crate) fn flatten_nested_let_recs(expr: &Expr) -> (Vec<LetRecBinding>, Expr) {
    let mut bindings = Vec::new();
    let mut next_fvar = 10_000u64;
    let body = flatten_expr(expr, &mut bindings, &mut next_fvar);
    (bindings, body)
}

pub(crate) fn encode_wf_recursion(binding: &LetRecBinding, metric: &TerminationMetric) -> Expr {
    let (measure, relation) = match metric {
        TerminationMetric::WellFounded { measure, relation } => (measure.clone(), relation.clone()),
        _ => (wf_placeholder_measure(), Expr::prop()),
    };
    let lambda_body = binding
        .params
        .iter()
        .rev()
        .fold(binding.body.clone(), |acc, (_, ty)| {
            Expr::lam(BinderInfo::Default, ty.clone(), acc)
        });
    let fix = Expr::const_(Name::from_string("WellFounded.fix"), vec![Level::zero()]);
    Expr::app(Expr::app(Expr::app(fix, measure), relation), lambda_body)
}

pub(crate) fn encode_structural_recursion(binding: &LetRecBinding, decreasing_arg: usize) -> Expr {
    let rec_name = binding
        .params
        .get(decreasing_arg)
        .and_then(|(_, ty)| inductive_type_name(ty))
        .map(|name| format!("{name}.rec"))
        .unwrap_or_else(|| "Nat.rec".into());
    let motive = binding.return_type.clone().unwrap_or_else(Expr::type_);
    let lambda_body = binding
        .params
        .iter()
        .rev()
        .fold(binding.body.clone(), |acc, (_, ty)| {
            Expr::lam(BinderInfo::Default, ty.clone(), acc)
        });
    let recursor = Expr::const_(Name::from_string(&rec_name), vec![Level::zero()]);
    let base = Expr::app(Expr::app(recursor, motive), lambda_body);
    binding
        .params
        .get(decreasing_arg)
        .map_or(base.clone(), |_| {
            Expr::app(
                base,
                Expr::bvar(binding.params.len().saturating_sub(decreasing_arg + 1) as u32),
            )
        })
}

pub(crate) fn topological_sort_bindings(
    dep_graph: &[Vec<usize>],
) -> Result<Vec<usize>, LetRecExtError> {
    let mut indegree: HashMap<usize, usize> = (0..dep_graph.len()).map(|idx| (idx, 0)).collect();
    let mut reverse = vec![Vec::new(); dep_graph.len()];
    for (node, deps) in dep_graph.iter().enumerate() {
        for dep in deps.iter().copied().filter(|dep| *dep < dep_graph.len()) {
            if let Some(entry) = indegree.get_mut(&node) {
                *entry += 1;
            }
            reverse[dep].push(node);
        }
    }
    let mut queue: Vec<usize> = indegree
        .iter()
        .filter_map(|(idx, deg)| (*deg == 0).then_some(*idx))
        .collect();
    queue.sort_unstable_by(|a, b| b.cmp(a));
    let mut order = Vec::with_capacity(dep_graph.len());
    while let Some(node) = queue.pop() {
        order.push(node);
        for dependent in reverse
            .get(node)
            .into_iter()
            .flat_map(|nodes| nodes.iter().copied())
        {
            if let Some(entry) = indegree.get_mut(&dependent) {
                if *entry > 0 {
                    *entry -= 1;
                    if *entry == 0 {
                        queue.push(dependent);
                        queue.sort_unstable_by(|a, b| b.cmp(a));
                    }
                }
            }
        }
    }
    if order.len() == dep_graph.len() {
        Ok(order)
    } else {
        Err(LetRecExtError::CyclicDependency {
            names: indegree
                .into_iter()
                .filter_map(|(idx, deg)| (deg > 0).then_some(format!("binding#{idx}")))
                .collect(),
        })
    }
}

fn collect_fvars(expr: &Expr, out: &mut HashSet<u64>) {
    match expr.kind() {
        ExprKind::FVar(id) => {
            out.insert(id.as_u64());
        }
        ExprKind::App(f, a) => {
            collect_fvars(f, out);
            collect_fvars(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_fvars(ty, out);
            collect_fvars(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_fvars(ty, out);
            collect_fvars(val, out);
            collect_fvars(body, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => collect_fvars(inner, out),
        _ => {}
    }
}

fn mentions_fvar(expr: &Expr, target: u64) -> bool {
    let mut fvars = HashSet::new();
    collect_fvars(expr, &mut fvars);
    fvars.contains(&target)
}

fn collect_recursive_calls(expr: &Expr, target: u64, out: &mut Vec<Vec<Expr>>) {
    if let Some((head, args)) = app_spine(expr) {
        if matches!(head.kind(), ExprKind::FVar(id) if id.as_u64() == target) {
            out.push(args.into_iter().cloned().collect());
        }
    }
    match expr.kind() {
        ExprKind::App(f, a) => {
            collect_recursive_calls(f, target, out);
            collect_recursive_calls(a, target, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_recursive_calls(ty, target, out);
            collect_recursive_calls(body, target, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_recursive_calls(ty, target, out);
            collect_recursive_calls(val, target, out);
            collect_recursive_calls(body, target, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            collect_recursive_calls(inner, target, out)
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
        ExprKind::Const(name, _) => Some(name.to_string()),
        ExprKind::App(f, _) => inductive_type_name(f),
        _ => None,
    }
}

fn find_partial_marker(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        ExprKind::Const(name, _) if is_partial_name(&name.to_string()) => Some(expr.clone()),
        ExprKind::App(f, a) => find_partial_marker(f).or_else(|| find_partial_marker(a)),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            find_partial_marker(ty).or_else(|| find_partial_marker(body))
        }
        ExprKind::Let(_, ty, val, body, _) => find_partial_marker(ty)
            .or_else(|| find_partial_marker(val))
            .or_else(|| find_partial_marker(body)),
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => find_partial_marker(inner),
        _ => None,
    }
}

fn contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == needle,
        ExprKind::App(f, a) => contains_const(f, needle) || contains_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_const(ty, needle) || contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_const(ty, needle)
                || contains_const(val, needle)
                || contains_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => contains_const(inner, needle),
        _ => false,
    }
}

fn is_partial_name(name: &str) -> bool {
    ["nomatch", "panic", "unreachable", "match.partial"]
        .iter()
        .any(|needle| name.contains(needle))
}

fn flatten_expr(expr: &Expr, acc: &mut Vec<LetRecBinding>, next_fvar: &mut u64) -> Expr {
    match expr.kind() {
        ExprKind::Let(name, ty, val, body, _) => {
            let flat_ty = flatten_expr(ty, acc, next_fvar);
            let flat_val = flatten_expr(val, acc, next_fvar);
            let (params, body_expr) = peel_lambdas(&flat_val);
            let fvar_id = *next_fvar;
            *next_fvar += 1;
            acc.push(LetRecBinding {
                name: name.to_string(),
                params,
                return_type: Some(flat_ty),
                body: body_expr,
                fvar_id,
            });
            flatten_expr(
                &body.instantiate(&Expr::fvar(clean_kernel::FVarId::new(fvar_id))),
                acc,
                next_fvar,
            )
        }
        ExprKind::App(f, a) => Expr::app(
            flatten_expr(f, acc, next_fvar),
            flatten_expr(a, acc, next_fvar),
        ),
        ExprKind::Lam(binder, ty, body) => Expr::lam(
            *binder,
            flatten_expr(ty, acc, next_fvar),
            flatten_expr(body, acc, next_fvar),
        ),
        ExprKind::Pi(binder, ty, body) => Expr::pi(
            *binder,
            flatten_expr(ty, acc, next_fvar),
            flatten_expr(body, acc, next_fvar),
        ),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj(name.clone(), *idx, flatten_expr(inner, acc, next_fvar))
        }
        ExprKind::MData(data, inner) => {
            Expr::mdata(data.clone(), flatten_expr(inner, acc, next_fvar))
        }
        _ => expr.clone(),
    }
}

fn peel_lambdas(expr: &Expr) -> (Vec<(String, Expr)>, Expr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let ExprKind::Lam(_, ty, body) = current.kind() {
        params.push((format!("arg{}", params.len()), ty.as_ref().clone()));
        current = body;
    }
    (params, current.clone())
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended type class synthesis: multi-parameter resolution, functional
//! dependencies, backtracking, overlap detection, default fallback, outparam
//! inference, trace generation, and stuck instance detection.
//!
//! Reference: Lean 4 `src/Lean/Meta/SynthInstance.lean`

use crate::instance_priority::DefaultInstanceFallback;
use crate::instances::{extract_class_app, InstanceInfo, InstanceTable};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use std::collections::HashMap;
use thiserror::Error;

/// Configuration for extended multi-parameter type class synthesis.
#[derive(Debug, Clone)]
pub(crate) struct ExtSynthConfig {
    pub(crate) max_depth: usize,
    pub(crate) max_heartbeats: usize,
    pub(crate) use_defaults: bool,
    pub(crate) trace_enabled: bool,
}

impl Default for ExtSynthConfig {
    fn default() -> Self {
        Self {
            max_depth: 32,
            max_heartbeats: 10_000,
            use_defaults: true,
            trace_enabled: false,
        }
    }
}

/// Errors from extended type class synthesis.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum ExtSynthError {
    #[error("No instance found for class `{0}`")]
    NoInstance(Name),
    #[error("Synthesis exceeded maximum depth ({0})")]
    MaxDepthExceeded(usize),
    #[error("Synthesis exceeded maximum heartbeats ({0})")]
    MaxHeartbeatsExceeded(usize),
    #[error("Goal type is not a class application")]
    NotClassApplication,
    #[error("Class `{0}` is not registered")]
    UnregisteredClass(Name),
    #[error("All {count} candidates failed for `{class_name}`")]
    AllCandidatesFailed { class_name: Name, count: usize },
    #[error("Instance stuck: class `{class_name}` has unresolved metavariables")]
    StuckInstance { class_name: Name },
    #[error("Functional dep conflict for `{class_name}` at param {param_idx}")]
    FunDepConflict { class_name: Name, param_idx: usize },
    #[error("Instance overlap: `{inst_a}` and `{inst_b}` for `{class_name}`")]
    InstanceOverlap {
        class_name: Name,
        inst_a: Name,
        inst_b: Name,
    },
}

/// A functional dependency: input parameter indices determine output indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FunDep {
    pub(crate) inputs: Vec<usize>,
    pub(crate) outputs: Vec<usize>,
}

/// Registry of functional dependencies for type classes.
#[derive(Debug, Clone, Default)]
pub(crate) struct FunDepRegistry {
    deps: HashMap<Name, Vec<FunDep>>,
}

impl FunDepRegistry {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn register(&mut self, class_name: Name, fundep: FunDep) {
        self.deps.entry(class_name).or_default().push(fundep);
    }

    #[must_use]
    pub(crate) fn get(&self, class_name: &Name) -> &[FunDep] {
        self.deps.get(class_name).map_or(&[], Vec::as_slice)
    }

    #[must_use]
    pub(crate) fn has_fundeps(&self, class_name: &Name) -> bool {
        self.deps.get(class_name).is_some_and(|v| !v.is_empty())
    }
}

/// A single entry in the resolution trace.
#[derive(Debug, Clone)]
pub(crate) struct ExtTraceEntry {
    pub(crate) class_name: Name,
    pub(crate) candidate: Name,
    pub(crate) depth: usize,
    pub(crate) outcome: ExtTraceOutcome,
}

/// Outcome recorded in a trace entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExtTraceOutcome {
    Success,
    StructuralMismatch,
    FunDepMismatch,
    Stuck,
    DefaultUsed,
    Skipped,
}

/// Mutable state for an extended synthesis session.
#[derive(Debug, Clone, Default)]
pub(crate) struct ExtSynthState {
    pub(crate) depth: usize,
    pub(crate) heartbeats: usize,
    pub(crate) trace: Vec<ExtTraceEntry>,
    pub(crate) cache: HashMap<String, Option<Expr>>,
}

impl ExtSynthState {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn success_count(&self) -> usize {
        self.trace
            .iter()
            .filter(|e| e.outcome == ExtTraceOutcome::Success)
            .count()
    }
}

/// Describes an instance overlap: two instances matching the same goal.
#[derive(Debug, Clone)]
pub(crate) struct OverlapInfo {
    pub(crate) class_name: Name,
    pub(crate) inst_a: Name,
    pub(crate) inst_b: Name,
    pub(crate) priority_a: u32,
    pub(crate) priority_b: u32,
}

/// Detect overlapping instances for a class in the instance table.
#[must_use]
pub(crate) fn detect_overlaps(class_name: &Name, instances: &InstanceTable) -> Vec<OverlapInfo> {
    let candidates = instances.get_instances(class_name);
    let mut overlaps = Vec::new();
    for (i, a) in candidates.iter().enumerate() {
        for b in &candidates[i + 1..] {
            let Some((_, args_a)) = extract_class_app(&a.type_) else {
                continue;
            };
            let Some((_, args_b)) = extract_class_app(&b.type_) else {
                continue;
            };
            if args_a.len() == args_b.len()
                && args_a
                    .iter()
                    .zip(args_b.iter())
                    .all(|(x, y)| structural_eq(x, y))
            {
                overlaps.push(OverlapInfo {
                    class_name: class_name.clone(),
                    inst_a: a.name.clone(),
                    inst_b: b.name.clone(),
                    priority_a: a.priority,
                    priority_b: b.priority,
                });
            }
        }
    }
    overlaps
}

/// Check if a goal has FVar arguments indicating stuck metavariables.
#[must_use]
pub(crate) fn is_stuck_goal(goal: &Expr) -> bool {
    let Some((_, args)) = extract_class_app(goal) else {
        return false;
    };
    args.iter().any(|a| matches!(a.kind(), ExprKind::FVar(_)))
}

/// Extended type class synthesizer with multi-parameter resolution, functional
/// dependency tracking, and backtracking.
pub(crate) struct ExtSynthesizer<'a> {
    instances: &'a InstanceTable,
    defaults: Option<&'a DefaultInstanceFallback>,
    fundeps: Option<&'a FunDepRegistry>,
    config: ExtSynthConfig,
}

impl<'a> ExtSynthesizer<'a> {
    pub(crate) fn new(
        instances: &'a InstanceTable,
        defaults: Option<&'a DefaultInstanceFallback>,
        fundeps: Option<&'a FunDepRegistry>,
        config: ExtSynthConfig,
    ) -> Self {
        Self {
            instances,
            defaults,
            fundeps,
            config,
        }
    }

    pub(crate) fn with_defaults(instances: &'a InstanceTable) -> Self {
        Self::new(instances, None, None, ExtSynthConfig::default())
    }

    /// Synthesize an instance for a (possibly multi-parameter) goal.
    pub(crate) fn synthesize(
        &self,
        goal: &Expr,
        state: &mut ExtSynthState,
    ) -> Result<Expr, ExtSynthError> {
        if is_stuck_goal(goal) {
            let cn = extract_class_app(goal)
                .map(|(n, _)| n)
                .unwrap_or_else(Name::anon);
            return Err(ExtSynthError::StuckInstance { class_name: cn });
        }
        self.synthesize_inner(goal, state)
    }

    /// Infer output parameters from a candidate using functional deps.
    #[must_use]
    pub(crate) fn infer_outparams(
        &self,
        class_name: &Name,
        candidate: &InstanceInfo,
    ) -> Vec<(usize, Expr)> {
        let fundeps = match self.fundeps {
            Some(r) => r.get(class_name),
            None => return Vec::new(),
        };
        let Some((_, inst_args)) = extract_class_app(&candidate.type_) else {
            return Vec::new();
        };
        let mut solutions = Vec::new();
        for fd in fundeps {
            for &out_idx in &fd.outputs {
                if let Some(expr) = inst_args.get(out_idx) {
                    solutions.push((out_idx, expr.clone()));
                }
            }
        }
        solutions
    }

    /// Generate a resolution trace summary (class, candidate) pairs.
    #[must_use]
    pub(crate) fn trace_summary(state: &ExtSynthState) -> Vec<(Name, Name)> {
        state
            .trace
            .iter()
            .filter(|e| e.outcome == ExtTraceOutcome::Success)
            .map(|e| (e.class_name.clone(), e.candidate.clone()))
            .collect()
    }

    fn synthesize_inner(
        &self,
        goal: &Expr,
        state: &mut ExtSynthState,
    ) -> Result<Expr, ExtSynthError> {
        if state.depth > self.config.max_depth {
            return Err(ExtSynthError::MaxDepthExceeded(self.config.max_depth));
        }
        if state.heartbeats > self.config.max_heartbeats {
            return Err(ExtSynthError::MaxHeartbeatsExceeded(
                self.config.max_heartbeats,
            ));
        }
        let (class_name, goal_args) =
            extract_class_app(goal).ok_or(ExtSynthError::NotClassApplication)?;
        let cache_key = format!("{goal:?}");
        if let Some(cached) = state.cache.get(&cache_key) {
            return cached.clone().ok_or(ExtSynthError::NoInstance(class_name));
        }
        if !self.instances.is_class(&class_name) {
            return Err(ExtSynthError::UnregisteredClass(class_name));
        }
        let out_params: Vec<usize> = self
            .instances
            .get_class(&class_name)
            .map(|info| info.out_params.clone())
            .unwrap_or_default();
        let regular = self.instances.get_instances(&class_name);
        let def_count = self
            .defaults
            .map_or(0, |d| d.get_defaults(&class_name).len());
        let total = regular.len() + def_count;
        if total == 0 {
            state.cache.insert(cache_key, None);
            return Err(ExtSynthError::NoInstance(class_name));
        }
        if let Some(r) = self.try_candidates(regular, &class_name, &goal_args, &out_params, state) {
            state.cache.insert(cache_key, Some(r.clone()));
            return Ok(r);
        }
        if self.config.use_defaults {
            if let Some(defaults) = self.defaults {
                let infos: Vec<InstanceInfo> = defaults
                    .get_defaults(&class_name)
                    .iter()
                    .map(|d| InstanceInfo {
                        name: d.name.clone(),
                        class_name: class_name.clone(),
                        expr: d.expr.clone(),
                        type_: d.type_.clone(),
                        priority: d.priority.value(),
                        synth_order: None,
                    })
                    .collect();
                if let Some(r) =
                    self.try_candidates(&infos, &class_name, &goal_args, &out_params, state)
                {
                    if self.config.trace_enabled {
                        state.trace.push(ExtTraceEntry {
                            class_name: class_name.clone(),
                            candidate: Name::anon(),
                            depth: state.depth,
                            outcome: ExtTraceOutcome::DefaultUsed,
                        });
                    }
                    state.cache.insert(cache_key, Some(r.clone()));
                    return Ok(r);
                }
            }
        }
        state.cache.insert(cache_key, None);
        Err(ExtSynthError::AllCandidatesFailed {
            class_name,
            count: total,
        })
    }

    fn try_candidates(
        &self,
        candidates: &[InstanceInfo],
        class_name: &Name,
        goal_args: &[Expr],
        out_params: &[usize],
        state: &mut ExtSynthState,
    ) -> Option<Expr> {
        for candidate in candidates {
            state.heartbeats += 1;
            if state.heartbeats > self.config.max_heartbeats {
                return None;
            }
            let result = self.try_candidate(candidate, goal_args, out_params, state);
            if self.config.trace_enabled {
                let outcome = if result.is_some() {
                    ExtTraceOutcome::Success
                } else {
                    ExtTraceOutcome::StructuralMismatch
                };
                state.trace.push(ExtTraceEntry {
                    class_name: class_name.clone(),
                    candidate: candidate.name.clone(),
                    depth: state.depth,
                    outcome,
                });
            }
            if result.is_some() {
                return result;
            }
        }
        None
    }

    fn try_candidate(
        &self,
        candidate: &InstanceInfo,
        goal_args: &[Expr],
        out_params: &[usize],
        state: &mut ExtSynthState,
    ) -> Option<Expr> {
        let (inst_class, inst_args) = extract_class_app(&candidate.type_)?;
        if inst_class != candidate.class_name || inst_args.len() != goal_args.len() {
            return None;
        }
        for (idx, (ia, ga)) in inst_args.iter().zip(goal_args.iter()).enumerate() {
            if out_params.contains(&idx) {
                continue;
            }
            if !structural_eq(ia, ga) {
                return None;
            }
        }
        if let Some(registry) = self.fundeps {
            for fd in registry.get(&candidate.class_name) {
                for &out_idx in &fd.outputs {
                    if out_params.contains(&out_idx) {
                        continue;
                    }
                    if let (Some(io), Some(go)) = (inst_args.get(out_idx), goal_args.get(out_idx)) {
                        if !structural_eq(io, go) {
                            return None;
                        }
                    }
                }
            }
        }
        if has_inst_implicit_prereqs(&candidate.type_) {
            state.depth += 1;
            let ok = self.resolve_prereqs(&candidate.type_, state);
            state.depth -= 1;
            if !ok {
                return None;
            }
        }
        Some(candidate.expr.clone())
    }

    fn resolve_prereqs(&self, ty: &Expr, state: &mut ExtSynthState) -> bool {
        let mut cur = ty;
        while let ExprKind::Pi(bd, arg_ty, body) = cur.kind() {
            if bd.info == clean_kernel::BinderInfo::InstImplicit
                && extract_class_app(arg_ty).is_some()
                && self.synthesize_inner(arg_ty, state).is_err()
            {
                return false;
            }
            cur = body.as_ref();
        }
        true
    }
}

/// Build a class application expression from a class name and arguments.
pub(crate) fn build_ext_class_app(class_name: &Name, args: &[Expr]) -> Expr {
    let mut result = Expr::const_(class_name.clone(), vec![]);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}

fn has_inst_implicit_prereqs(ty: &Expr) -> bool {
    let mut cur = ty;
    while let ExprKind::Pi(bd, _, body) = cur.kind() {
        if bd.info == clean_kernel::BinderInfo::InstImplicit {
            return true;
        }
        cur = body.as_ref();
    }
    false
}

fn structural_eq(a: &Expr, b: &Expr) -> bool {
    match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            structural_eq(f1, f2) && structural_eq(a1, a2)
        }
        (ExprKind::Lam(bi1, ty1, b1), ExprKind::Lam(bi2, ty2, b2))
        | (ExprKind::Pi(bi1, ty1, b1), ExprKind::Pi(bi2, ty2, b2)) => {
            bi1 == bi2 && structural_eq(ty1, ty2) && structural_eq(b1, b2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        _ => false,
    }
}

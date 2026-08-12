// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced type class synthesis with backtracking, dependency resolution,
//! and output parameter propagation.
//!
//! Extends [`crate::instance_resolution`] / [`crate::instance_synthesis`] with:
//! backtracking search, instance unification, dependency-aware synthesis,
//! default instance fallback, outParam propagation, synthesis cache, depth
//! limiting, and synthesis tracing.
//!
//! Reference: Lean 4 `src/Lean/Meta/SynthInstance.lean`

use crate::instance_priority::DefaultInstanceFallback;
use crate::instances::{extract_class_app, InstanceInfo, InstanceTable};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use std::collections::HashMap;
use thiserror::Error;

/// Configuration for enhanced type class synthesis.
#[derive(Debug, Clone)]
pub(crate) struct TcSynthConfig {
    /// Maximum recursion depth for nested synthesis.
    pub(crate) max_depth: usize,
    /// Maximum candidate trials before giving up.
    pub(crate) max_heartbeats: usize,
    /// Whether to try default instances as fallback.
    pub(crate) use_default_instances: bool,
    /// Whether to propagate outParam solutions.
    pub(crate) propagate_out_params: bool,
    /// Whether to enable synthesis tracing.
    pub(crate) trace_enabled: bool,
}

impl Default for TcSynthConfig {
    fn default() -> Self {
        Self {
            max_depth: 32,
            max_heartbeats: 10_000,
            use_default_instances: true,
            propagate_out_params: true,
            trace_enabled: false,
        }
    }
}

/// Errors from enhanced type class synthesis.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum TcSynthError {
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
    #[error("Unification failed for all {count} candidates of `{class_name}`")]
    AllCandidatesFailed { class_name: Name, count: usize },
    #[error("Dependency synthesis failed: {class_name} requires {dep_class}")]
    DependencyFailed { class_name: Name, dep_class: Name },
}

/// A single step in the synthesis trace.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct SynthTraceEntry {
    pub(crate) class_name: Name,
    pub(crate) candidate: Name,
    pub(crate) depth: usize,
    pub(crate) outcome: SynthOutcome,
}

/// Outcome of trying a single candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SynthOutcome {
    Success,
    StructuralMismatch,
    DependencyFailed,
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    Skipped,
}

/// Mutable state tracked during a single synthesis session.
#[derive(Debug, Clone, Default)]
pub(crate) struct TcSynthState {
    pub(crate) depth: usize,
    pub(crate) heartbeats: usize,
    pub(crate) trace: Vec<SynthTraceEntry>,
    pub(crate) cache: HashMap<String, Option<Expr>>,
}

impl TcSynthState {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn with_cache(cache: HashMap<String, Option<Expr>>) -> Self {
        Self {
            cache,
            ..Self::default()
        }
    }

    #[must_use]
    pub(crate) fn success_count(&self) -> usize {
        self.trace
            .iter()
            .filter(|e| e.outcome == SynthOutcome::Success)
            .count()
    }

    #[must_use]
    pub(crate) fn cache_size(&self) -> usize {
        self.cache.len()
    }
}

/// A dependency requirement for synthesis (e.g., `[Add a]` prerequisite).
#[derive(Debug, Clone)]
pub(crate) struct SynthDependency {
    pub(crate) class_name: Name,
    pub(crate) args: Vec<Expr>,
}

/// Enhanced type class synthesizer with backtracking and dependency resolution.
///
/// Performs structural matching on an [`InstanceTable`] with optional
/// [`DefaultInstanceFallback`]. For full unification, use
/// [`crate::instance_synthesis::synthesize_instance`].
pub(crate) struct TcSynthesizer<'a> {
    instances: &'a InstanceTable,
    defaults: Option<&'a DefaultInstanceFallback>,
    config: TcSynthConfig,
}

impl<'a> TcSynthesizer<'a> {
    pub(crate) fn new(
        instances: &'a InstanceTable,
        defaults: Option<&'a DefaultInstanceFallback>,
        config: TcSynthConfig,
    ) -> Self {
        Self {
            instances,
            defaults,
            config,
        }
    }

    pub(crate) fn with_defaults(instances: &'a InstanceTable) -> Self {
        Self::new(instances, None, TcSynthConfig::default())
    }

    /// Synthesize an instance for the given goal type.
    pub(crate) fn synthesize(
        &self,
        goal: &Expr,
        state: &mut TcSynthState,
    ) -> Result<Expr, TcSynthError> {
        self.synthesize_inner(goal, state)
    }

    /// Fast-path check: does the class have any candidates?
    #[must_use]
    pub(crate) fn has_candidates(&self, goal: &Expr) -> bool {
        let Some((class_name, _)) = extract_class_app(goal) else {
            return false;
        };
        if !self.instances.is_class(&class_name) {
            return false;
        }
        let has_regular = !self.instances.get_instances(&class_name).is_empty();
        let has_defaults = self.defaults.is_some_and(|d| d.has_defaults(&class_name));
        has_regular || has_defaults
    }

    /// Synthesize with dependency chain resolution.
    pub(crate) fn synthesize_with_deps(
        &self,
        goal: &Expr,
        deps: &[SynthDependency],
        state: &mut TcSynthState,
    ) -> Result<Expr, TcSynthError> {
        for dep in deps {
            let dep_goal = build_class_app(&dep.class_name, &dep.args);
            let _ = self.synthesize_inner(&dep_goal, state).map_err(|_| {
                let (class_name, _) = extract_class_app(goal).unwrap_or((Name::anon(), vec![]));
                TcSynthError::DependencyFailed {
                    class_name,
                    dep_class: dep.class_name.clone(),
                }
            })?;
        }
        self.synthesize_inner(goal, state)
    }

    fn synthesize_inner(
        &self,
        goal: &Expr,
        state: &mut TcSynthState,
    ) -> Result<Expr, TcSynthError> {
        if state.depth > self.config.max_depth {
            return Err(TcSynthError::MaxDepthExceeded(self.config.max_depth));
        }
        if state.heartbeats > self.config.max_heartbeats {
            return Err(TcSynthError::MaxHeartbeatsExceeded(
                self.config.max_heartbeats,
            ));
        }

        let (class_name, goal_args) =
            extract_class_app(goal).ok_or(TcSynthError::NotClassApplication)?;

        // Cache lookup
        let cache_key = format!("{goal:?}");
        if let Some(cached) = state.cache.get(&cache_key) {
            return cached.clone().ok_or(TcSynthError::NoInstance(class_name));
        }

        if !self.instances.is_class(&class_name) {
            return Err(TcSynthError::UnregisteredClass(class_name));
        }

        let out_param_indices: Vec<usize> = self
            .instances
            .get_class(&class_name)
            .map(|info| info.out_params.clone())
            .unwrap_or_default();

        let regular = self.instances.get_instances(&class_name);
        let candidate_count = regular.len()
            + self
                .defaults
                .map_or(0, |d| d.get_defaults(&class_name).len());

        if candidate_count == 0 {
            state.cache.insert(cache_key, None);
            return Err(TcSynthError::NoInstance(class_name));
        }

        // Try regular instances in priority order
        if let Some(r) =
            self.try_candidates(regular, &class_name, &goal_args, &out_param_indices, state)
        {
            state.cache.insert(cache_key, Some(r.clone()));
            return Ok(r);
        }

        // Try default instances as fallback
        if self.config.use_default_instances {
            if let Some(defaults) = self.defaults {
                let default_infos: Vec<InstanceInfo> = defaults
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
                if let Some(r) = self.try_candidates(
                    &default_infos,
                    &class_name,
                    &goal_args,
                    &out_param_indices,
                    state,
                ) {
                    state.cache.insert(cache_key, Some(r.clone()));
                    return Ok(r);
                }
            }
        }

        state.cache.insert(cache_key, None);
        Err(TcSynthError::AllCandidatesFailed {
            class_name,
            count: candidate_count,
        })
    }

    /// Try a list of candidates, returning the first successful match.
    fn try_candidates(
        &self,
        candidates: &[InstanceInfo],
        class_name: &Name,
        goal_args: &[Expr],
        out_param_indices: &[usize],
        state: &mut TcSynthState,
    ) -> Option<Expr> {
        for candidate in candidates {
            state.heartbeats += 1;
            if state.heartbeats > self.config.max_heartbeats {
                return None;
            }
            let outcome = self.try_candidate(candidate, goal_args, out_param_indices, state);
            if self.config.trace_enabled {
                state.trace.push(SynthTraceEntry {
                    class_name: class_name.clone(),
                    candidate: candidate.name.clone(),
                    depth: state.depth,
                    outcome: if outcome.is_some() {
                        SynthOutcome::Success
                    } else {
                        SynthOutcome::StructuralMismatch
                    },
                });
            }
            if outcome.is_some() {
                return outcome;
            }
        }
        None
    }

    /// Try a single candidate via structural matching with outParam handling.
    fn try_candidate(
        &self,
        candidate: &InstanceInfo,
        goal_args: &[Expr],
        out_param_indices: &[usize],
        state: &mut TcSynthState,
    ) -> Option<Expr> {
        let (inst_class, inst_args) = extract_class_app(&candidate.type_)?;
        if inst_class != candidate.class_name || inst_args.len() != goal_args.len() {
            return None;
        }

        // Phase 1: Check non-outParam args structurally
        for (idx, (inst_arg, goal_arg)) in inst_args.iter().zip(goal_args.iter()).enumerate() {
            if self.config.propagate_out_params && out_param_indices.contains(&idx) {
                continue;
            }
            if !structural_eq(inst_arg, goal_arg) {
                return None;
            }
        }

        // Check inst-implicit prerequisites
        if has_inst_implicit_prereqs(&candidate.type_) {
            state.depth += 1;
            let prereq_ok = self.resolve_prereqs(&candidate.type_, state);
            state.depth -= 1;
            if !prereq_ok {
                if self.config.trace_enabled {
                    state.trace.push(SynthTraceEntry {
                        class_name: candidate.class_name.clone(),
                        candidate: candidate.name.clone(),
                        depth: state.depth,
                        outcome: SynthOutcome::DependencyFailed,
                    });
                }
                return None;
            }
        }
        Some(candidate.expr.clone())
    }

    /// Resolve inst-implicit prerequisites by walking the Pi-binder chain.
    fn resolve_prereqs(&self, candidate_type: &Expr, state: &mut TcSynthState) -> bool {
        let mut current = candidate_type;
        while let ExprKind::Pi(bd, arg_ty, body) = current.kind() {
            if bd.info == clean_kernel::BinderInfo::InstImplicit
                && extract_class_app(arg_ty).is_some()
                && self.synthesize_inner(arg_ty, state).is_err()
            {
                return false;
            }
            current = body.as_ref();
        }
        true
    }
}

// ---------------------------------------------------------------------------
// Free helpers
// ---------------------------------------------------------------------------

/// Build a class application expression from a class name and arguments.
pub(crate) fn build_class_app(class_name: &Name, args: &[Expr]) -> Expr {
    let mut result = Expr::const_(class_name.clone(), vec![]);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}

fn has_inst_implicit_prereqs(ty: &Expr) -> bool {
    let mut current = ty;
    while let ExprKind::Pi(bd, _, body) = current.kind() {
        if bd.info == clean_kernel::BinderInfo::InstImplicit {
            return true;
        }
        current = body.as_ref();
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
        (ExprKind::Lam(bi1, ty1, body1), ExprKind::Lam(bi2, ty2, body2))
        | (ExprKind::Pi(bi1, ty1, body1), ExprKind::Pi(bi2, ty2, body2)) => {
            bi1 == bi2 && structural_eq(ty1, ty2) && structural_eq(body1, body2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        _ => false,
    }
}

/// Extract outParam solutions from a successful candidate match.
#[must_use]
pub(crate) fn extract_out_param_solutions(
    candidate: &InstanceInfo,
    out_param_indices: &[usize],
) -> Vec<(usize, Expr)> {
    let Some((_, inst_args)) = extract_class_app(&candidate.type_) else {
        return Vec::new();
    };
    out_param_indices
        .iter()
        .filter_map(|&idx| inst_args.get(idx).map(|expr| (idx, expr.clone())))
        .collect()
}

/// Propagate outParam solutions into goal arguments.
#[must_use]
pub(crate) fn propagate_out_params(goal_args: &[Expr], solutions: &[(usize, Expr)]) -> Vec<Expr> {
    let mut result = goal_args.to_vec();
    for (idx, expr) in solutions {
        if *idx < result.len() {
            result[*idx] = expr.clone();
        }
    }
    result
}

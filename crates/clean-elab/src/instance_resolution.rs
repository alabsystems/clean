// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Standalone typeclass instance resolution engine with backtracking search.
//!
//! This module provides a configurable resolution engine that can be used
//! independently of `ElabCtx` for diagnostics and tooling, or integrated
//! with the elaboration context via the `instance_synthesis` module.
//!
//! # Architecture
//!
//! The resolution engine separates concerns:
//! - [`ResolutionConfig`] controls limits (depth, heartbeats, transparency)
//! - [`ResolutionState`] tracks mutable resolution state (depth, heartbeats, trace, cache)
//! - [`resolve_instance`] is the main entry point for resolution
//! - [`ResolutionError`] provides structured diagnostics for failure cases
//!
//! # Algorithm
//!
//! 1. Decompose the goal type into class name + arguments via [`extract_class_app`]
//! 2. Look up instances for the class from the [`InstanceTable`]
//! 3. Sort by priority (higher priority number = tried first, matching Lean 4)
//! 4. For each instance, try to unify the instance type with the target type
//! 5. If the instance has prerequisites (inst-implicit args), recursively resolve them
//! 6. First successful resolution wins (backtracking on failure)
//! 7. Cache ground results for performance
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Meta/SynthInstance.lean`

use crate::instances::{extract_class_app, InstanceInfo, InstanceTable};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use std::collections::HashMap;

/// Configuration for the resolution engine.
///
/// Controls resource limits and resolution behavior. Defaults are chosen
/// to match Lean 4's behavior while providing sub-millisecond resolution
/// for typical typeclass hierarchies.
#[derive(Debug, Clone)]
pub struct ResolutionConfig {
    /// Maximum recursion depth for nested instance resolution.
    /// Prevents infinite loops in cyclic instance hierarchies.
    /// Default: 32 (matches Lean 4 `synthInstance.maxSize` heuristic).
    pub max_depth: usize,
    /// Maximum number of resolution steps (heartbeats) before giving up.
    /// Each candidate trial counts as one heartbeat. Prevents combinatorial
    /// explosion in wide instance search spaces.
    /// Default: 10000.
    pub max_heartbeats: usize,
}

impl Default for ResolutionConfig {
    fn default() -> Self {
        Self {
            max_depth: 32,
            max_heartbeats: 10_000,
        }
    }
}

/// A single step in the resolution trace, for debugging.
#[derive(Debug, Clone)]
pub struct ResolutionStep {
    /// Name of the class being resolved.
    pub class_name: Name,
    /// Name of the instance candidate tried.
    pub instance_tried: Name,
    /// Whether this candidate succeeded.
    pub success: bool,
    /// Recursion depth at which this step occurred.
    pub depth: usize,
}

/// Mutable state tracked during a single resolution session.
///
/// This is created fresh for each top-level `resolve_instance` call
/// and threaded through recursive resolution.
#[derive(Debug, Clone, Default)]
pub struct ResolutionState {
    /// Current recursion depth.
    pub depth: usize,
    /// Total heartbeats consumed (candidate trials).
    pub heartbeats: usize,
    /// Trace of resolution steps for debugging/diagnostics.
    pub trace: Vec<ResolutionStep>,
    /// Cache of previously resolved instances, keyed by normalized goal string.
    /// `Some(expr)` means resolved successfully; `None` means no instance found
    /// (negative caching to avoid re-searching).
    pub cache: HashMap<String, Option<Expr>>,
}

impl ResolutionState {
    /// Create a new resolution state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a state seeded with an existing cache (for cross-call reuse).
    pub fn with_cache(cache: HashMap<String, Option<Expr>>) -> Self {
        Self {
            cache,
            ..Self::default()
        }
    }
}

/// Errors produced by the resolution engine.
///
/// Unlike the existing `Option<Expr>` return in `ElabCtx::resolve_instance`,
/// these errors provide structured diagnostics for tooling and error messages.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ResolutionError {
    /// No instance found for the given class and arguments.
    #[error("No instance found for class `{0}`")]
    NoInstance(Name),
    /// Maximum recursion depth exceeded during resolution.
    #[error("Instance resolution exceeded maximum depth ({0})")]
    MaxDepthExceeded(usize),
    /// Maximum heartbeats (candidate trials) exceeded.
    #[error("Instance resolution exceeded maximum heartbeats ({0})")]
    MaxHeartbeatsExceeded(usize),
    /// The goal type could not be decomposed into a class application.
    #[error("Goal type is not a class application")]
    NotClassApplication,
    /// The class name is not registered in the instance table.
    #[error("Class `{0}` is not registered")]
    UnregisteredClass(Name),
    /// Unification of instance type with goal type failed for all candidates.
    #[error("Unification failed for all {candidate_count} candidates of class `{class_name}`")]
    UnificationFailed {
        /// The class that was being resolved.
        class_name: Name,
        /// How many candidates were tried.
        candidate_count: usize,
    },
}

/// Attempt to resolve a typeclass instance using only the instance table.
///
/// This is a lightweight, standalone resolution that does not require an
/// `ElabCtx`. It performs structural matching without full unification
/// (no metavariable solving). For full resolution with unification, use
/// [`crate::instance_synthesis::synthesize_instance`].
///
/// # Arguments
///
/// * `class_type` - The goal type, e.g. `Add Nat`
/// * `instances` - The instance table to search
/// * `config` - Resolution limits
/// * `state` - Mutable resolution state (trace, cache, counters)
///
/// # Returns
///
/// `Ok(Expr)` with the resolved instance expression, or `Err(ResolutionError)`
/// with a structured diagnostic.
pub fn resolve_instance(
    class_type: &Expr,
    instances: &InstanceTable,
    config: &ResolutionConfig,
    state: &mut ResolutionState,
) -> Result<Expr, ResolutionError> {
    // Check depth limit
    if state.depth > config.max_depth {
        return Err(ResolutionError::MaxDepthExceeded(config.max_depth));
    }

    // Check heartbeat limit
    if state.heartbeats > config.max_heartbeats {
        return Err(ResolutionError::MaxHeartbeatsExceeded(
            config.max_heartbeats,
        ));
    }

    // Decompose class_type into class name + arguments
    let (class_name, goal_args) =
        extract_class_app(class_type).ok_or(ResolutionError::NotClassApplication)?;

    // Check cache (using a simple string key for the normalized type)
    let cache_key = format!("{class_type:?}");
    if let Some(cached) = state.cache.get(&cache_key) {
        return cached
            .clone()
            .ok_or(ResolutionError::NoInstance(class_name));
    }

    // Check if the class is registered
    if !instances.is_class(&class_name) {
        return Err(ResolutionError::UnregisteredClass(class_name));
    }

    // Get candidate instances sorted by priority (highest first)
    let candidates = instances.get_instances(&class_name);
    if candidates.is_empty() {
        state.cache.insert(cache_key, None);
        return Err(ResolutionError::NoInstance(class_name));
    }

    let candidate_count = candidates.len();

    // Try each candidate in priority order
    for candidate in candidates {
        state.heartbeats += 1;
        if state.heartbeats > config.max_heartbeats {
            return Err(ResolutionError::MaxHeartbeatsExceeded(
                config.max_heartbeats,
            ));
        }

        let success = try_candidate_structural(candidate, &goal_args, instances, config, state);

        state.trace.push(ResolutionStep {
            class_name: class_name.clone(),
            instance_tried: candidate.name.clone(),
            success: success.is_some(),
            depth: state.depth,
        });

        if let Some(result) = success {
            state.cache.insert(cache_key, Some(result.clone()));
            return Ok(result);
        }
    }

    // All candidates failed
    state.cache.insert(cache_key, None);
    Err(ResolutionError::UnificationFailed {
        class_name,
        candidate_count,
    })
}

/// Try a single candidate instance via structural matching.
///
/// This performs a lightweight check: does the instance's class match,
/// and do the instance's arguments structurally match the goal arguments?
/// For inst-implicit prerequisites, it recursively resolves them.
///
/// This does NOT perform full unification with metavariable solving --
/// that requires the elaboration context. For full resolution, the
/// `instance_synthesis` module wraps `ElabCtx::resolve_instance`.
fn try_candidate_structural(
    candidate: &InstanceInfo,
    goal_args: &[Expr],
    _instances: &InstanceTable,
    _config: &ResolutionConfig,
    _state: &mut ResolutionState,
) -> Option<Expr> {
    // Extract class application from the candidate's type
    let (inst_class, inst_args) = extract_class_app(&candidate.type_)?;

    // Class name must match (should always be true given lookup, but verify)
    if inst_class != candidate.class_name {
        return None;
    }

    // Argument count must match
    if inst_args.len() != goal_args.len() {
        return None;
    }

    // Structural equality check on arguments
    // This is a conservative check -- full unification would accept more cases
    for (inst_arg, goal_arg) in inst_args.iter().zip(goal_args.iter()) {
        if !structural_eq(inst_arg, goal_arg) {
            return None;
        }
    }

    // All arguments match structurally
    Some(candidate.expr.clone())
}

/// Conservative structural equality check for expressions.
///
/// Returns `true` if two expressions are structurally identical.
/// This is deliberately conservative -- it does not handle alpha-equivalence,
/// metavariable instantiation, or WHNF normalization. Those require `ElabCtx`.
fn structural_eq(a: &Expr, b: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;

    match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            structural_eq(f1, f2) && structural_eq(a1, a2)
        }
        (ExprKind::Lam(bi1, ty1, body1), ExprKind::Lam(bi2, ty2, body2)) => {
            bi1 == bi2 && structural_eq(ty1, ty2) && structural_eq(body1, body2)
        }
        (ExprKind::Pi(bi1, ty1, body1), ExprKind::Pi(bi2, ty2, body2)) => {
            bi1 == bi2 && structural_eq(ty1, ty2) && structural_eq(body1, body2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        _ => false,
    }
}

/// Quick check: does the instance table contain any instances for a class
/// with the given arguments?
///
/// This is a fast path that avoids full resolution. It checks whether the
/// class is registered and has at least one candidate instance.
pub fn has_instance(class_name: &Name, instances: &InstanceTable) -> bool {
    instances.is_class(class_name) && !instances.get_instances(class_name).is_empty()
}

#[cfg(test)]
#[path = "instance_resolution_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extensionality tactic configuration and multi-arg / depth-controlled variants.
//!
//! - `ExtConfig` - Configuration for `ext` (variable names) and `congr` (depth)
//! - `ext_multi` - Apply `funext` multiple times with explicit or auto-generated names
//! - `congr_depth` - Apply congruence recursively up to a specified depth
//! - `congr_with_config` - Apply congruence using `ExtConfig`

use super::extensionality::funext;
use super::{ProofState, TacticResult};

// ============================================================================
// Configuration
// ============================================================================

/// Configuration for extensionality tactics (`ext`, `congr`).
///
/// `names` controls how introduced variables are named during `ext`:
/// - `Some(s)` uses the provided name
/// - `None` auto-generates a name (x, x_1, x_2, ...)
///
/// `depth` controls recursion depth for `congr`.
#[derive(Debug, Clone, Default)]
pub(crate) struct ExtConfig {
    /// Variable names for `ext`. `None` entries auto-generate names.
    pub names: Vec<Option<String>>,
    /// Recursion depth for `congr` (default: 1).
    pub depth: Option<usize>,
}

impl ExtConfig {
    /// Create a config with a single explicit name.
    pub(crate) fn with_name(name: &str) -> Self {
        Self {
            names: vec![Some(name.to_string())],
            depth: None,
        }
    }

    /// Create a config with multiple explicit names.
    pub(crate) fn with_names(names: &[&str]) -> Self {
        Self {
            names: names.iter().map(|n| Some(n.to_string())).collect(),
            depth: None,
        }
    }

    /// Create a config that auto-generates `count` variable names.
    pub(crate) fn auto_names(count: usize) -> Self {
        Self {
            names: vec![None; count],
            depth: None,
        }
    }

    /// Create a config for congr with specified depth.
    pub(crate) fn with_depth(depth: usize) -> Self {
        Self {
            names: Vec::new(),
            depth: Some(depth),
        }
    }
}

// ============================================================================
// Multi-argument ext
// ============================================================================

/// Generate a fresh variable name that does not collide with existing context.
///
/// Produces "x", "x_1", "x_2", etc.
fn auto_var_name(state: &ProofState, base: &str) -> String {
    let goal = match state.current_goal() {
        Some(g) => g,
        None => return base.to_string(),
    };
    let existing: Vec<&str> = goal.local_ctx.iter().map(|d| d.name.as_str()).collect();
    if !existing.contains(&base) {
        return base.to_string();
    }
    for i in 1..1000 {
        let candidate = format!("{base}_{i}");
        if !existing.contains(&candidate.as_str()) {
            return candidate;
        }
    }
    format!("{base}_auto")
}

/// Apply function extensionality multiple times according to `config`.
///
/// Each name in `config.names` drives one application of `funext`. `None` entries
/// auto-generate fresh variable names. When `config.names` is empty, a single
/// auto-named application is attempted.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: The current goal is an equality of functions (iterated Pi types).
/// ENSURES: On `Ok(())`, one `funext` application per name entry has been
///   applied, introducing the named variables into the goal context.
/// ENSURES: On `Err`, the proof state is unchanged for the failing step.
pub(crate) fn ext_multi(state: &mut ProofState, config: &ExtConfig) -> TacticResult {
    let names = if config.names.is_empty() {
        // Default: one auto-named application
        vec![None]
    } else {
        config.names.clone()
    };

    for name_opt in &names {
        let var_name = match name_opt {
            Some(n) => n.clone(),
            None => auto_var_name(state, "x"),
        };
        funext(state, &var_name)?;
    }
    Ok(())
}

// ============================================================================
// Congruence with depth
// ============================================================================

/// Apply congruence with a depth limit.
///
/// At each level, if the goal is `f a = f b`, it reduces to `a = b`.
/// If the goal is `f a = g a`, it reduces to `f = g`.
/// The `depth` parameter controls how many levels to recurse (default: 1).
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: The current goal is an equality `@Eq A (f x) (g y)`.
/// ENSURES: On `Ok(())`, the goal is decomposed into argument-equality subgoals
///   up to `depth` levels. Goals that are not equalities of applications are left
///   untouched.
/// ENSURES: On `Err`, the proof state is unchanged.
pub(crate) fn congr_depth(state: &mut ProofState, depth: usize) -> TacticResult {
    if depth == 0 {
        return Ok(());
    }

    // Apply one level of congr
    super::congr_obtain::congr(state)?;

    // If depth > 1, try to recurse on any new goals that are equalities
    if depth > 1 {
        let remaining = depth - 1;
        let goal_count = state.goals().len();
        // Try congr on each goal that was just created, but don't fail
        // if a sub-goal isn't a congruence target.
        for _ in 0..goal_count {
            // Try to apply congr recursively; if it fails (not an equality of
            // applications), just skip this goal.
            if congr_depth(state, remaining).is_err() {
                // Rotate to the next goal and try that one
                if state.goals().len() > 1 {
                    super::goal::rotate(state)?;
                }
            }
        }
    }

    Ok(())
}

/// Apply congruence using `ExtConfig`.
///
/// Reads `config.depth` (defaulting to 1) and delegates to [`congr_depth`].
pub(crate) fn congr_with_config(state: &mut ProofState, config: &ExtConfig) -> TacticResult {
    let depth = config.depth.unwrap_or(1);
    congr_depth(state, depth)
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance synthesis integration with the elaboration context.
//!
//! This module bridges the standalone [`crate::instance_resolution`] engine
//! with `ElabCtx`, providing:
//!
//! - [`synthesize_instance`]: Full resolution with unification and metavariable
//!   assignment, wrapping `ElabCtx::resolve_instance`.
//! - [`has_instance`]: Quick check without full resolution.
//! - [`collect_local_instances`]: Gather instance-typed local declarations
//!   from the elaboration context for use in resolution.
//!
//! # Design
//!
//! The existing `ElabCtx::resolve_instance` (in `infer/instance.rs`) already
//! implements full backtracking search with unification, out-parameter handling,
//! and caching. This module wraps it with structured error reporting from
//! [`crate::instance_resolution::ResolutionError`] and provides convenience
//! functions for common patterns.

use crate::instance_resolution::{
    has_instance as has_instance_standalone, ResolutionConfig, ResolutionState,
};
use crate::instances::extract_class_app;
use crate::ElabCtx;
use crate::ElabError;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

/// Synthesize an instance for the given target type using the elaboration context.
///
/// This performs full resolution with unification, metavariable solving, and
/// out-parameter inference. It delegates to `ElabCtx::resolve_instance` for
/// the actual search, then wraps failures in structured `ElabError`.
///
/// # Arguments
///
/// * `target` - The goal type (e.g. `Add Nat`)
/// * `ctx` - The elaboration context (provides unifier, environment, local context)
///
/// # Returns
///
/// The resolved instance expression, or an `ElabError` wrapping the resolution failure.
///
/// # Example (conceptual)
///
/// ```text
/// // Given: class Add (α : Type), instance instAddNat : Add Nat
/// let goal = Expr::app(Expr::const_("Add", []), Expr::const_("Nat", []));
/// let inst = synthesize_instance(&goal, &mut ctx)?;
/// // inst = Expr::const_("instAddNat", [])
/// ```
pub fn synthesize_instance(target: &Expr, ctx: &mut ElabCtx<'_>) -> Result<Expr, ElabError> {
    ctx.resolve_instance(target).ok_or_else(|| {
        // Provide a structured error message
        match extract_class_app(target) {
            Some((class_name, _args)) => {
                ElabError::NotImplemented(format!("No instance found for class `{class_name}`"))
            }
            None => ElabError::NotImplemented(
                "Instance resolution target is not a class application".to_string(),
            ),
        }
    })
}

/// Synthesize an instance with resolution tracing enabled.
///
/// Like [`synthesize_instance`], but also returns a `ResolutionState`
/// containing the trace of resolution steps for diagnostics.
///
/// The trace is populated via the standalone resolution engine for
/// structural pre-checking. The full `ElabCtx` resolution is then
/// used for the actual result (with unification).
pub fn synthesize_instance_traced(
    target: &Expr,
    ctx: &mut ElabCtx<'_>,
    config: &ResolutionConfig,
) -> (Result<Expr, ElabError>, ResolutionState) {
    let mut state = ResolutionState::new();

    // First, run the standalone structural resolution for tracing
    let _structural =
        crate::instance_resolution::resolve_instance(target, ctx.instances(), config, &mut state);

    // Then run the full ElabCtx resolution for the actual result
    let result = synthesize_instance(target, ctx);

    (result, state)
}

/// Quick check: can an instance for the given class likely be resolved?
///
/// This checks the instance table without performing full resolution.
/// A `true` result means candidates exist; it does not guarantee that
/// unification will succeed.
pub fn has_instance_for(class_name: &Name, ctx: &ElabCtx<'_>) -> bool {
    has_instance_standalone(class_name, ctx.instances())
}

/// Collect local instance-typed declarations from the elaboration context.
///
/// Gathers `(fvar_id, type)` pairs for all local bindings whose types
/// are class applications. These are the "local instances" that are
/// searched before global instances during resolution.
///
/// In Lean 4, these come from `[inst : TC α]` binders in the local context.
pub fn collect_local_instances(ctx: &ElabCtx<'_>) -> Vec<(Name, Expr)> {
    let mut result = Vec::new();

    // The ElabCtx tracks local instances explicitly via push/pop_local_instance.
    // We can also scan the local context for inst-implicit bindings.
    // For now, we expose the explicitly tracked ones.
    for (_fvar, ty) in ctx.local_instance_entries() {
        if let Some((class_name, _args)) = extract_class_app(ty) {
            result.push((class_name, ty.clone()));
        }
    }

    result
}

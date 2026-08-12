// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pre-definition intermediate representation for well-founded recursion.
//!
//! A `PreDefinition` captures the elaborated type and body of a recursive
//! function before the well-founded recursion encoding transforms it into
//! a `WellFounded.fix` application.
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/Basic.lean`

use clean_parser::SurfaceExpr;

/// Pre-definition: a fully elaborated function before WF encoding.
///
/// Captures all the information needed to transform a recursive function
/// into a `WellFounded.fix` application.
#[cfg(test)]
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct PreDefinition {
    /// Fully qualified declaration name.
    pub(crate) name: clean_kernel::name::Name,
    /// Universe parameter names.
    pub(crate) universe_params: Vec<clean_kernel::name::Name>,
    /// Elaborated type (with all binders as Pi).
    pub(crate) ty: clean_kernel::Expr,
    /// Elaborated value (with all binders as Lambda).
    pub(crate) val: clean_kernel::Expr,
}

/// Termination measure for well-founded recursion.
///
/// Represents the user-provided `termination_by` expression that maps
/// function arguments to a well-ordered domain (typically `Nat` via `sizeOf`).
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct TerminationMeasure {
    /// Parameter names bound in the measure expression.
    /// These correspond to the function's arguments that appear in the measure.
    pub(crate) params: Vec<String>,
    /// The measure expression itself (surface syntax to be elaborated).
    pub(crate) measure_expr: Box<SurfaceExpr>,
    /// Optional `decreasing_by` tactic for proving termination obligations.
    /// When `None`, the default cascade (simp_arith -> mathverse -> sorry) is used.
    pub(crate) decreasing_by: Option<Box<SurfaceExpr>>,
}

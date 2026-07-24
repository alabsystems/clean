// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder, termination hint, and open-path types for surface syntax.

use super::expr::SurfaceExpr;
use super::span::Span;

/// Binder information for surface syntax
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SurfaceBinderInfo {
    /// Explicit: `(x : T)`
    #[default]
    Explicit,
    /// Implicit: `{x : T}`
    Implicit,
    /// Strict implicit: `{{x : T}}` or `⦃x : T⦄`
    StrictImplicit,
    /// Instance: `[x : T]`
    Instance,
}

// ============================================================================
// Termination Hints
// ============================================================================

/// Kind of termination strategy requested by the user.
///
/// Lean 4.11.0+ supports explicit structural recursion via `termination_by structural <param>`.
/// Reference: <https://lean-lang.org/doc/reference/latest/releases/v4.11.0/>
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum TerminationKind {
    /// Well-founded recursion (default): `termination_by args => measure`
    #[default]
    WellFounded,
    /// Structural recursion: `termination_by structural <param>`
    /// The inner String is the parameter name to recurse on.
    Structural(String),
    /// Query mode: `termination_by?` - asks Lean to show inferred termination
    Query,
}

/// Termination measure hint for recursive definitions
///
/// Lean 4 syntax variants:
/// - `termination_by args => measure` (well-founded with measure)
/// - `termination_by measure` (well-founded, new syntax)
/// - `termination_by structural x` (structural recursion on param x)
/// - `termination_by?` (query: show inferred termination)
///
/// Example: `termination_by x y => x.length + y.length`
///
/// Reference: Leonardo de Moura et al., "Theorem Proving in Lean 4: Induction and Recursion",
/// <https://leanprover.github.io/theorem_proving_in_lean4/Induction-and-Recursion/>
#[derive(Debug, Clone)]
pub struct TerminationBy {
    /// Source location of the entire termination_by clause
    pub span: Span,
    /// Kind of termination (well-founded, structural, or query)
    pub kind: TerminationKind,
    /// Parameter names bound in the measure (may be empty for newer syntax or structural)
    pub params: Vec<String>,
    /// The termination measure expression (None for structural or query)
    pub measure: Option<Box<SurfaceExpr>>,
}

/// Decreasing proof tactic for recursive definitions
///
/// Lean 4 syntax: `decreasing_by tactic`
/// Example: `decreasing_by simp_arith`
///
/// Used when the automatic well-founded recursion proof fails and a manual
/// proof of the decreasing measure is needed.
#[derive(Debug, Clone)]
pub struct DecreasingBy {
    /// Source location of the entire decreasing_by clause
    pub span: Span,
    /// The tactic expression for proving the decreasing measure
    pub tactic: Box<SurfaceExpr>,
}

/// Combined termination hints for a recursive definition
///
/// Both hints are optional and may appear in any order after the definition body.
#[derive(Debug, Clone, Default)]
pub struct TerminationHints {
    /// Explicit termination measure: `termination_by x y => x + y`
    pub termination_by: Option<TerminationBy>,
    /// Explicit decreasing proof: `decreasing_by simp_arith`
    pub decreasing_by: Option<DecreasingBy>,
}

/// A binder in surface syntax
#[derive(Debug, Clone)]
pub struct SurfaceBinder {
    pub span: Span,
    /// Binder name (can be "_" for anonymous)
    pub name: String,
    /// Optional type annotation
    pub ty: Option<Box<SurfaceExpr>>,
    /// Optional default value (e.g., `(x := 5)` or `(x : Nat := 5)`)
    pub default: Option<Box<SurfaceExpr>>,
    /// Binder kind (explicit, implicit, instance)
    pub info: SurfaceBinderInfo,
}

impl SurfaceBinder {
    /// Create a new surface binder.
    ///
    /// # ENSURES
    /// - `span` is dummy (0, 0)
    /// - `default` is None
    pub fn new(name: impl Into<String>, ty: Option<SurfaceExpr>, info: SurfaceBinderInfo) -> Self {
        Self {
            span: Span::dummy(),
            name: name.into(),
            ty: ty.map(Box::new),
            default: None,
            info,
        }
    }

    /// Create an explicit binder `(name : ty)`.
    ///
    /// # ENSURES
    /// - `info == SurfaceBinderInfo::Explicit`
    pub fn explicit(name: impl Into<String>, ty: SurfaceExpr) -> Self {
        Self::new(name, Some(ty), SurfaceBinderInfo::Explicit)
    }

    /// Create an implicit binder `{name : ty}`.
    ///
    /// # ENSURES
    /// - `info == SurfaceBinderInfo::Implicit`
    pub fn implicit(name: impl Into<String>, ty: SurfaceExpr) -> Self {
        Self::new(name, Some(ty), SurfaceBinderInfo::Implicit)
    }

    /// Create an instance binder `[name : ty]`.
    ///
    /// # ENSURES
    /// - `info == SurfaceBinderInfo::Instance`
    pub fn instance(name: impl Into<String>, ty: SurfaceExpr) -> Self {
        Self::new(name, Some(ty), SurfaceBinderInfo::Instance)
    }
}

/// Renaming entry in an open command.
#[derive(Debug, Clone)]
pub struct OpenRename {
    pub from: String,
    pub to: String,
}

/// Path opened with optional selective names
#[derive(Debug, Clone)]
pub struct OpenPath {
    pub path: Vec<String>,
    pub names: Vec<String>,
    pub hiding: Vec<String>,
    pub renaming: Vec<OpenRename>,
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended inductive type specifications, positivity checking, and analysis.
//!
//! Defines the extended-level types (`InductiveSpec`, `ConstructorSpec`,
//! `MutualInductiveSpec`) and core analysis functions (positivity checking,
//! recursive arg computation, universe inference) for Lean 4 parity
//! (Epic #3082).
//!
//! The elaboration pipeline that consumes these types lives in
//! `inductive_ext_elab.rs`.
//!
//! Lean 4 reference: `src/kernel/inductive.cpp`, `src/Lean/Elab/Inductive.lean`.

use clean_kernel::inductive::mentions_name;
use clean_kernel::{Expr, ExprKind, Level, Name};

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for extended inductive type elaboration.
///
/// Controls which features are enabled during elaboration of complex
/// inductive types (nested, mutual, indexed).
#[derive(Debug, Clone)]
pub(crate) struct InductiveElabConfig {
    /// Whether to check strict positivity of recursive occurrences.
    pub(crate) check_positivity: bool,
    /// Whether to allow nested inductive types (e.g., `List Tree` in a `Tree` ctor).
    pub(crate) allow_nested: bool,
    /// Whether to allow mutual inductive blocks with multiple types.
    pub(crate) allow_mutual: bool,
    /// Maximum number of parameters for a single inductive type.
    pub(crate) max_params: usize,
}

impl Default for InductiveElabConfig {
    fn default() -> Self {
        Self {
            check_positivity: true,
            allow_nested: true,
            allow_mutual: true,
            max_params: 16,
        }
    }
}

// =============================================================================
// Specifications
// =============================================================================

/// Specification for a single inductive type at the elaboration level.
///
/// This is the extended representation that includes nested/recursive
/// classification and index tracking beyond what `InductiveTypeInfo` provides.
#[derive(Debug, Clone)]
pub(crate) struct InductiveSpec {
    pub(crate) name: Name,
    /// Parameters: `(name, type)` pairs shared across all constructors.
    pub(crate) params: Vec<(Name, Expr)>,
    /// Indices: `(name, type)` pairs that vary per constructor return type.
    pub(crate) indices: Vec<(Name, Expr)>,
    /// The full type former: `params -> indices -> Sort u`.
    pub(crate) type_: Expr,
    /// Constructor specifications.
    pub(crate) ctors: Vec<ConstructorSpec>,
    /// Whether any constructor field references this type.
    pub(crate) is_recursive: bool,
    /// Whether any constructor field applies a container to this type
    /// (e.g., `List T` where `T` is the inductive being defined).
    pub(crate) is_nested: bool,
}

/// Specification for a constructor within an extended inductive.
#[derive(Debug, Clone)]
pub(crate) struct ConstructorSpec {
    pub(crate) name: Name,
    /// Fields: `(name, type, is_recursive)`.
    pub(crate) fields: Vec<(Name, Expr, bool)>,
    /// The full constructor type including params.
    pub(crate) type_: Expr,
}

/// Specification for a mutual inductive block at the extended level.
#[derive(Debug, Clone)]
pub(crate) struct MutualInductiveSpec {
    pub(crate) inductives: Vec<InductiveSpec>,
    pub(crate) universe_params: Vec<Name>,
}

// =============================================================================
// Results
// =============================================================================

/// Result of elaborating a single extended inductive type.
#[derive(Debug, Clone)]
pub(crate) struct InductiveResult {
    /// The inductive declaration expression (type former).
    pub(crate) decl: Expr,
    /// The recursor expression.
    pub(crate) recursor: Expr,
    /// `casesOn` auxiliary (generated for types with constructors).
    pub(crate) cases_on: Option<Expr>,
    /// `noConfusion` auxiliary (generated for non-Prop types with >=1 ctor).
    pub(crate) no_confusion: Option<Expr>,
}

/// Result of elaborating a mutual inductive block.
#[derive(Debug, Clone)]
pub(crate) struct MutualInductiveResult {
    pub(crate) results: Vec<InductiveResult>,
    pub(crate) mutual_recursors: Vec<Expr>,
}

// =============================================================================
// Positivity errors
// =============================================================================

/// Describes what kind of positivity violation was found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PositivityViolation {
    /// The type appears to the left of an arrow in a constructor field.
    NegativeOccurrence,
    /// The type appears in a non-strictly-positive position
    /// (e.g., `(T -> X) -> T` where T is under a function domain).
    NonStrictlyPositive,
    /// The type appears inside a nested container in a non-positive position.
    InNestedNonPositive,
}

/// Error from a failed positivity check with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PositivityError {
    /// The constructor where the violation was found.
    pub(crate) ctor: Name,
    /// The index of the offending parameter within the constructor.
    pub(crate) param_index: usize,
    /// The kind of violation.
    pub(crate) violation: PositivityViolation,
}

impl std::fmt::Display for PositivityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match &self.violation {
            PositivityViolation::NegativeOccurrence => "negative occurrence",
            PositivityViolation::NonStrictlyPositive => "non-strictly-positive occurrence",
            PositivityViolation::InNestedNonPositive => "non-positive in nested container",
        };
        write!(
            f,
            "positivity violation in constructor {}: {} at parameter {}",
            self.ctor, kind, self.param_index
        )
    }
}

// =============================================================================
// Core analysis functions
// =============================================================================

/// Check strict positivity for an `InductiveSpec`.
///
/// Examines each constructor field type to verify that the inductive type
/// being defined only appears in strictly positive positions.
pub(crate) fn check_strict_positivity(spec: &InductiveSpec) -> Result<(), PositivityError> {
    for ctor in &spec.ctors {
        for (idx, (_, field_ty, _)) in ctor.fields.iter().enumerate() {
            if has_negative_occurrence(&spec.name, field_ty) {
                return Err(PositivityError {
                    ctor: ctor.name.clone(),
                    param_index: idx,
                    violation: classify_violation(&spec.name, field_ty),
                });
            }
        }
    }
    Ok(())
}

/// Classify what kind of positivity violation exists in a type.
fn classify_violation(ind_name: &Name, ty: &Expr) -> PositivityViolation {
    match ty.kind() {
        ExprKind::Pi(_, domain, body) => {
            if mentions_name(domain, ind_name) {
                if is_nested_application(domain, ind_name) {
                    PositivityViolation::InNestedNonPositive
                } else {
                    PositivityViolation::NegativeOccurrence
                }
            } else {
                classify_violation(ind_name, body)
            }
        }
        _ => PositivityViolation::NonStrictlyPositive,
    }
}

/// Check if a type expression contains a negative occurrence of `name`.
///
/// A name occurs negatively if it appears to the left of an arrow (Pi domain)
/// at any nesting depth.
fn has_negative_occurrence(name: &Name, ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, domain, body) => {
            if mentions_name(domain, name) {
                return true;
            }
            has_negative_occurrence(name, body)
        }
        _ => false,
    }
}

/// Check if an expression is a nested application involving `name`
/// (e.g., `List name` or `Prod name X`).
fn is_nested_application(expr: &Expr, name: &Name) -> bool {
    let head = expr.get_app_fn();
    if let ExprKind::Const(head_name, _) = head.kind() {
        if head_name != name {
            return expr
                .get_app_args()
                .iter()
                .any(|arg| mentions_name(arg, name));
        }
    }
    false
}

/// Compute which constructor arguments are recursive.
///
/// Returns indices (0-based, relative to fields only, excluding params)
/// of fields whose types mention the inductive type name.
pub(crate) fn compute_rec_args(spec: &InductiveSpec) -> Vec<usize> {
    let mut rec_indices = Vec::new();
    for ctor in &spec.ctors {
        for (idx, (_, field_ty, _)) in ctor.fields.iter().enumerate() {
            if mentions_name(field_ty, &spec.name) {
                rec_indices.push(idx);
            }
        }
    }
    rec_indices
}

/// Infer the result universe of an inductive type from its parameters
/// and constructor field types.
///
/// The result universe is `imax` of all constructor field universes. For a
/// Prop-valued inductive, this may collapse to `0`.
pub(crate) fn infer_inductive_universe(
    params: &[(Name, Expr)],
    ctors: &[ConstructorSpec],
) -> Level {
    if ctors.is_empty() {
        return Level::zero();
    }

    let mut result = Level::zero();
    for ctor in ctors {
        for (_, field_ty, _) in &ctor.fields {
            let field_level = extract_universe_from_type(field_ty);
            result = Level::imax(result, field_level);
        }
    }

    // Account for parameter universes
    for (_, param_ty) in params {
        let param_level = extract_universe_from_type(param_ty);
        result = Level::imax(result, param_level);
    }

    result
}

/// Extract the universe level from a type expression by stripping Pi binders
/// and reading the Sort level.
pub(crate) fn extract_universe_from_type(expr: &Expr) -> Level {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    match current.kind() {
        ExprKind::Sort(level) => level.clone(),
        _ => Level::zero(),
    }
}

/// Check if a type expression is Prop (Sort 0).
pub(crate) fn is_prop_type(ty: &Expr) -> bool {
    let mut current = ty;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    matches!(current.kind(), ExprKind::Sort(l) if l.is_zero())
}

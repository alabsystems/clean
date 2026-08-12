// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! String interpolation elaboration for s!, m!, and f! notation.
//!
//! Lean 4 supports three interpolated string kinds:
//!
//! - `s!"Hello {name}"` → `String.append "Hello " (toString name)`
//! - `f!"x = {x}"` → `Format.append (Format.text "x = ") (format x)`
//! - `m!"error: {msg}"` → `MessageData.ofFormat (Format.append (Format.text "error: ") (format msg))`
//!
//! The parser stores these as `SurfaceExpr::InterpolatedStr { kind, parts }` where
//! parts are `InterpolationPart::Literal(String)` or `InterpolationPart::Expr(SurfaceExpr)`.
//!
//! This module provides the elaboration-side entry point that:
//! 1. Desugars `InterpolatedStr` into nested function application AST
//! 2. Recursively elaborates the desugared expression
//!
//! The actual desugaring logic lives in `clean_parser::interpolation` to keep
//! parser and elaborator concerns separated. This module re-exports the key
//! types and provides the elaboration bridge.

use crate::error::ElabError;
use clean_kernel::Expr;
use clean_parser::interpolation::{
    desugar_interpolation, desugar_prefixed_interpolation_parts, InterpolationPart,
};
use clean_parser::InterpolatedStringKind;

/// Desugar and elaborate an interpolated string expression.
///
/// Takes the parsed interpolation `kind` and `parts` from a
/// `SurfaceExpr::InterpolatedStr` node and produces a kernel `Expr`
/// by first desugaring into nested function applications, then
/// recursively elaborating the result.
///
/// # Desugaring rules
///
/// ## `s!` (String interpolation)
/// - Literal parts become `String` literals
/// - Expression parts get wrapped in `toString`
/// - Parts are joined with `String.append`
///
/// ## `f!` (Format interpolation)
/// - Literal parts become `Format.text "..."` applications
/// - Expression parts get wrapped in `format`
/// - Parts are joined with `Format.append`
///
/// ## `m!` (MessageData interpolation)
/// - Same as `f!` desugaring, then wrapped in `MessageData.ofFormat`
///
/// # Examples
///
/// ```text
/// s!"Hello {name}" →
///   String.append "Hello " (toString name)
///
/// s!"{a} + {b} = {c}" →
///   String.append (toString a)
///     (String.append " + "
///       (String.append (toString b)
///         (String.append " = " (toString c))))
///
/// m!"{msg}" →
///   MessageData.ofFormat (format msg)
/// ```
///
/// # REQUIRES
/// - `parts` are well-formed `InterpolationPart` values from the parser
/// - `ctx` has a valid environment with `toString`, `String.append`, etc.
///   (or stubs) registered when elaborating `s!` strings
///
/// # ENSURES
/// - On success, returns a kernel `Expr` corresponding to the desugared form
/// - All sub-expressions within interpolation braces are fully elaborated
pub(crate) fn elaborate_interpolation(
    ctx: &mut crate::infer::ElabCtx<'_>,
    kind: InterpolatedStringKind,
    parts: &[InterpolationPart],
) -> Result<Expr, ElabError> {
    let desugared = desugar_prefixed_interpolation_parts(kind, parts);
    ctx.elaborate(&desugared)
}

/// Desugar interpolation parts for `s!` strings only.
///
/// Convenience wrapper around `clean_parser::interpolation::desugar_interpolation`
/// that takes a slice reference rather than an owned Vec. This avoids cloning
/// when the caller only needs the desugared surface expression without
/// elaboration.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn desugar_s_interpolation(parts: &[InterpolationPart]) -> clean_parser::SurfaceExpr {
    desugar_interpolation(parts.to_vec())
}

/// Desugar interpolation parts for any kind (s!, f!, m!).
///
/// Thin wrapper that re-exports `desugar_prefixed_interpolation_parts` under
/// a name scoped to this module.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn desugar_by_kind(
    kind: InterpolatedStringKind,
    parts: &[InterpolationPart],
) -> clean_parser::SurfaceExpr {
    desugar_prefixed_interpolation_parts(kind, parts)
}

/// Check whether an interpolation has any expression parts.
///
/// Returns `true` if all parts are literals (no `{expr}` segments).
/// Useful for optimizing the common case of `s!"plain string"` which
/// can be elaborated as a simple string literal without the `toString`/
/// `String.append` overhead.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn is_plain_literal(parts: &[InterpolationPart]) -> bool {
    parts
        .iter()
        .all(|part| matches!(part, InterpolationPart::Literal(_)))
}

/// Extract the concatenated literal text when all parts are literals.
///
/// Returns `None` if any part is an expression interpolation.
/// When `Some`, the caller can emit a single string literal instead of
/// the full `String.append` chain.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn try_extract_plain_text(parts: &[InterpolationPart]) -> Option<String> {
    if !is_plain_literal(parts) {
        return None;
    }
    let mut text = String::new();
    for part in parts {
        if let InterpolationPart::Literal(s) = part {
            text.push_str(s);
        }
    }
    Some(text)
}

/// Count the number of expression interpolations in the parts list.
///
/// Useful for diagnostics and complexity estimation.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn count_interpolated_exprs(parts: &[InterpolationPart]) -> usize {
    parts
        .iter()
        .filter(|part| matches!(part, InterpolationPart::Expr(_)))
        .count()
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! String interpolation elaboration for s!, m!, and f! notation.
//!
//! Lean 4 supports three interpolated string kinds:
//!
//! - `s!"Hello {name}"` → `((ToString.toString "Hello " ++ ToString.toString name) : String)`
//! - `f!"x = {x}"` → `Format.append (Format.text "x = ") (format x)`
//! - `m!"error: {msg}"` → `((Lean.ToMessageData.toMessageData "error: " ++ Lean.ToMessageData.toMessageData msg) : Lean.MessageData)`
//!   (Lean's own `m!` macro, `Lean/Message.lean`)
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
/// - Nonempty literal parts and expression parts use canonical `ToString.toString`
/// - Converted parts are joined left-associatively with hygienic `HAppend.hAppend`
/// - An empty interpolation converts `""`; the whole result is ascribed `String`
///
/// ## `f!` (Format interpolation)
/// - Literal parts become `Format.text "..."` applications
/// - Expression parts get wrapped in `format`
/// - Parts are joined with `Format.append`
///
/// ## `m!` (MessageData interpolation)
/// - Every chunk, literal or `{e}`, becomes `Lean.ToMessageData.toMessageData chunk`; empty
///   literals are skipped; chunks are joined left-associatively with `++` and
///   the whole is ascribed `Lean.MessageData` (Lean's `m!` macro)
///
/// # Examples
///
/// ```text
/// s!"Hello {name}" →
///   ((ToString.toString "Hello " ++ ToString.toString name) : String)
///
/// s!"{a} + {b}" →
///   (((ToString.toString a ++ ToString.toString " + ")
///       ++ ToString.toString b) : String)
///
/// m!"{msg}" →
///   (Lean.ToMessageData.toMessageData msg : Lean.MessageData)
/// ```
///
/// # REQUIRES
/// - `parts` are well-formed `InterpolationPart` values from the parser
/// - `ctx` supplies `ToString.toString`, `HAppend.hAppend`, `String`, and the
///   actual required typeclass instances when elaborating `s!` strings
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
/// This describes the chunks, not an elaboration shortcut: even a literal-only
/// `s!` must use its actual `ToString String` instance.
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
/// The returned text does not replace interpolation elaboration: conversion
/// and append instances may give the original chunks observable behavior.
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

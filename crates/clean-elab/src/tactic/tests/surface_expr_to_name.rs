// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for `surface_expr_to_name` — #3529.
//!
//! Before the fix, dotted identifiers like `StateT.bind` / `Except.ok.injEq`
//! parsed as `SurfaceExpr::Proj` hit the `_ => format!("{other:?}")` arm
//! and were Debug-rendered into span-bearing strings. Every downstream
//! consumer (`simp only [...]`, `simp only [...] at h`, `rw`, `cases`,
//! `induction`) then failed to resolve the name in the environment, and
//! the tactic reported `NoProgress`. These tests pin the Proj-flattening
//! behaviour so future refactors cannot silently regress it.

use crate::tactic::builtins::surface_expr_to_name;
use clean_parser::{Projection, Span, SurfaceExpr};

fn span() -> Span {
    Span::dummy()
}

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(span(), name.to_string())
}

fn proj(base: SurfaceExpr, field: &str) -> SurfaceExpr {
    SurfaceExpr::Proj(span(), Box::new(base), Projection::Named(field.to_string()))
}

#[test]
fn plain_ident_preserves_text() {
    assert_eq!(surface_expr_to_name(&ident("foo")), "foo");
}

#[test]
fn single_proj_flattens_to_dotted_name() {
    // `StateT.bind` — two-segment qualified name, the core #3529 case.
    let expr = proj(ident("StateT"), "bind");
    assert_eq!(surface_expr_to_name(&expr), "StateT.bind");
}

#[test]
fn nested_proj_flattens_recursively() {
    // `Except.ok.injEq` — three-segment qualified name.
    let expr = proj(proj(ident("Except"), "ok"), "injEq");
    assert_eq!(surface_expr_to_name(&expr), "Except.ok.injEq");
}

#[test]
fn parenthesised_ident_strips_parens() {
    let expr = SurfaceExpr::Paren(span(), Box::new(ident("foo")));
    assert_eq!(surface_expr_to_name(&expr), "foo");
}

#[test]
fn parenthesised_proj_still_flattens() {
    let expr = SurfaceExpr::Paren(span(), Box::new(proj(ident("StateT"), "bind")));
    assert_eq!(surface_expr_to_name(&expr), "StateT.bind");
}

/// Guard: if someone "simplifies" `surface_expr_to_name` back to the
/// Ident-only match, the returned string for a Proj will contain the
/// Debug-rendered span, which always includes `Span { ` or similar. None
/// of these substrings should ever appear in the output.
#[test]
fn proj_output_never_contains_debug_artefacts() {
    let expr = proj(ident("StateT"), "bind");
    let out = surface_expr_to_name(&expr);
    assert!(!out.contains("Span"), "leaked Debug span: {out}");
    assert!(!out.contains("Proj"), "leaked variant name: {out}");
    assert!(!out.contains('{'), "leaked Debug braces: {out}");
}

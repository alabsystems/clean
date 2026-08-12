// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Desugaring of `where` local definitions into nested `let rec` expressions.
//!
//! Lean 4 supports `where` clauses that introduce local definitions after a
//! definition body:
//!
//! ```text
//! def foo (n : Nat) : Nat :=
//!   bar n
//! where
//!   bar (x : Nat) : Nat := x + 1
//! ```
//!
//! This is desugared into nested `let rec` bindings wrapping the body:
//!
//! ```text
//! def foo (n : Nat) : Nat :=
//!   let rec bar (x : Nat) : Nat := x + 1
//!   in bar n
//! ```
//!
//! Multiple where clauses desugar to nested `let rec` with earlier definitions
//! visible to later ones and all definitions visible in the body.
//!
//! NOTE: the production entry point is
//! [`crate::where_desugar_ext::desugar_where_from_parsed_ordered`], which adds
//! dependency ordering and loud duplicate/cycle rejection on top of the same
//! per-clause `LetRec` builder. This module keeps the plain source-order
//! variant (shared [`WhereClause`] type + unit tests of the builder contract).
//!
//! Reference: Lean 4 `src/Lean/Parser/Term.lean:701-703` (`whereDecls`),
//! `src/Lean/Elab/Binders.lean:472-476` (`expandWhereDecls` — `where` becomes
//! a leading `let rec` group), `src/Lean/Elab/MutualDef.lean:332-397`.

use clean_parser::{Span, SurfaceBinder, SurfaceExpr, WhereLocalDef};

/// A single local definition from a `where` clause.
///
/// Represents a parsed where definition like:
/// ```text
/// bar (x : Nat) : Nat := x + 1
/// ```
#[derive(Debug, Clone)]
pub(crate) struct WhereClause {
    /// Name of the local definition
    pub(crate) name: String,
    /// Parameters (binders) of the local definition
    pub(crate) params: Vec<SurfaceBinder>,
    /// Optional return type annotation
    pub(crate) return_type: Option<SurfaceExpr>,
    /// Body expression of the local definition
    pub(crate) body: SurfaceExpr,
    /// Source span of the entire where clause
    pub(crate) span: Span,
}

/// Desugar `where` clauses into nested `let rec` expressions wrapping the body.
///
/// Given `body` and a list of `where` clauses, produces a `SurfaceExpr` where
/// each clause becomes a `let rec` binding. Clauses are wrapped outside-in so
/// that earlier clauses are visible to later ones, and all clauses are visible
/// in the original body.
///
/// # Example
///
/// Input:
/// ```text
/// body = bar n
/// clauses = [
///   bar (x : Nat) : Nat := x + 1,
///   baz (y : Nat) : Nat := bar y + 1,
/// ]
/// ```
///
/// Output:
/// ```text
/// let rec bar : (x : Nat) → Nat := fun (x : Nat) => (x + 1 : Nat) in
/// let rec baz : (y : Nat) → Nat := fun (y : Nat) => (bar y + 1 : Nat) in
/// bar n
/// ```
///
/// # REQUIRES
/// - `clauses` is non-empty (if empty, returns body unchanged)
/// - Each clause has a non-empty name
///
/// # ENSURES
/// - Returns a `SurfaceExpr` equivalent to nested `LetRec` wrapping `body`
/// - Earlier clauses are visible to later clauses and to the body
/// - Parameter binders are converted to a lambda wrapping the clause body
/// - An ascribed return type rides inside the lambda as an `Ascription` on
///   the clause body AND as the binder's full `params → ret` Pi annotation;
///   an unannotated clause leaves the binder type `None` (inferred). See
///   [`crate::where_desugar_ext::build_let_rec`] for the shape contract.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn desugar_where(body: SurfaceExpr, clauses: &[WhereClause]) -> SurfaceExpr {
    if clauses.is_empty() {
        return body;
    }

    // Wrap from the last clause inward so that earlier clauses scope over later ones.
    // After folding: let rec clause[0] in (let rec clause[1] in (... in body))
    clauses.iter().rev().fold(body, |inner, clause| {
        crate::where_desugar_ext::build_let_rec(clause, inner)
    })
}

/// Desugar `where` local definitions from the parser AST into nested `let rec`.
///
/// Converts parser `WhereLocalDef` types into internal `WhereClause` types and
/// delegates to [`desugar_where`]. This is the entry point used by the elaborator
/// when processing `SurfaceDecl::Def` and `SurfaceDecl::Theorem` with `where` blocks.
///
/// # REQUIRES
/// - `body` is the main definition body expression
/// - `where_defs` is the parsed where-clause local definitions from the parser
///
/// # ENSURES
/// - Returns a `SurfaceExpr` with nested `LetRec` wrapping the body
/// - Empty `where_defs` returns the body unchanged
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn desugar_where_from_parsed(
    body: &SurfaceExpr,
    where_defs: &[WhereLocalDef],
) -> SurfaceExpr {
    if where_defs.is_empty() {
        return body.clone();
    }

    let clauses: Vec<WhereClause> = where_defs
        .iter()
        .map(|def| WhereClause {
            name: def.name.clone(),
            params: def.binders.clone(),
            return_type: def.ret_ty.as_deref().cloned(),
            body: def.body.clone(),
            span: def.span,
        })
        .collect();

    desugar_where(body.clone(), &clauses)
}

#[cfg(test)]
#[path = "where_desugar_tests.rs"]
mod tests;

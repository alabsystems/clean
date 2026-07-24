// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level where clause elaboration.
//!
//! Transforms where-clause declarations into nested `Expr::let_named`
//! expressions. Unlike [`where_desugar`](crate::where_desugar) which operates
//! on surface syntax (`SurfaceExpr`), this module works on already-elaborated
//! kernel [`Expr`] values.
//!
//! # Lean 4 Reference
//!
//! In Lean 4, a `where` block introduces local definitions after a definition
//! body. During elaboration, these are desugared into nested `let` bindings
//! that wrap the body expression. Each where declaration produces one
//! `let_named` binding with the declaration's name, type, and value.
//!
//! ```text
//! def foo (n : Nat) : Nat :=
//!   bar n
//! where
//!   bar (x : Nat) : Nat := x + 1
//!
//! -- elaborates to:
//! def foo (n : Nat) : Nat :=
//!   let bar : Nat → Nat := fun x => x + 1
//!   bar n
//! ```

use clean_kernel::name::Name;
use clean_kernel::Expr;

/// A single declaration from a `where` clause, at the kernel level.
///
/// Represents one local definition with a name, optional type annotation,
/// and a value expression. When the type is `None`, the elaborator should
/// infer it from the value.
#[derive(Debug, Clone)]
pub(crate) struct WhereDecl {
    /// The name of the local binding (e.g., `bar`).
    pub(crate) name: Name,
    /// Optional type annotation. `None` means infer from value.
    pub(crate) type_: Option<Expr>,
    /// The value expression (the right-hand side of `:=`).
    pub(crate) value: Expr,
}

/// A collection of where-clause declarations.
///
/// Wraps a vector of [`WhereDecl`] for ergonomic construction and
/// transformation.
#[derive(Debug, Clone)]
pub(crate) struct WhereClause {
    /// The ordered list of where declarations.
    pub(crate) decls: Vec<WhereDecl>,
}

impl WhereClause {
    /// Create an empty where clause.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { decls: Vec::new() }
    }

    /// Create a where clause from a list of declarations.
    #[must_use]
    pub(crate) fn from_decls(decls: Vec<WhereDecl>) -> Self {
        Self { decls }
    }

    /// Check if this where clause is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }
}

/// Lift where declarations into nested `let_named` bindings wrapping a body.
///
/// Given a body expression and a slice of `(name, type, value)` tuples, wraps
/// the body in nested `Expr::let_named` from outermost to innermost. Earlier
/// declarations scope over later ones and the body.
///
/// # Example
///
/// ```text
/// lift_where_to_let(body, &[
///   (bar, Nat → Nat, fun x => x + 1),
///   (baz, Nat → Nat, fun y => bar y),
/// ])
/// // => let bar : Nat → Nat := fun x => x + 1 in
/// //    let baz : Nat → Nat := fun y => bar y in
/// //    body
/// ```
///
/// # REQUIRES
/// - `type_` expressions are well-typed kernel expressions
/// - `value` expressions are well-typed kernel expressions
///
/// # ENSURES
/// - Returns `body` unchanged if `where_decls` is empty
/// - Each where declaration becomes one `let_named` binding
/// - Earlier declarations scope over later ones (nested inside-out)
/// - `non_dep` is `false` for all let bindings (conservative default)
pub(crate) fn lift_where_to_let(body: Expr, where_decls: &[(Name, Expr, Expr)]) -> Expr {
    if where_decls.is_empty() {
        return body;
    }

    // Fold from the last declaration inward: the first declaration is the
    // outermost let, scoping over all subsequent declarations and the body.
    where_decls
        .iter()
        .rev()
        .fold(body, |inner, (name, ty, val)| {
            Expr::let_named(
                name.clone(),
                ty.clone(),
                val.clone(),
                inner,
                false, // non_dep = false (conservative: assume body may depend on binding)
            )
        })
}

#[cfg(test)]
#[path = "where_clause_tests.rs"]
mod tests;

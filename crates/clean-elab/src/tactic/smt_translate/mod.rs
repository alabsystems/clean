// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expr→SMT-LIB2 string translator for SMT proof verification.
//!
//! Mirrors `AyBackend::translate_expr_inner()` (ay_backend.rs:751-917) but
//! outputs SMT-LIB2 strings instead of ay `Term` objects. This enables
//! `AyProofBackend` (which operates on SMT-LIB strings) to be used from
//! `SmtSolver::Verifiable` for proof extraction and verification.
//!
//! Part of #2091 Phase 1.5. See designs/2026-03-01-smt-proof-verification-pipeline.md

mod classified;
mod const_app;
mod core;

use clean_kernel::expr::Literal;
use clean_kernel::{Expr, ExprKind, FVarId};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TranslateError {
    #[error("unsupported expression kind for SMT-LIB: {0}")]
    UnsupportedExpr(String),
}

/// Sort of a declared SMT-LIB variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtSort {
    Int,
    Bool,
    Real,
}

impl SmtSort {
    fn smtlib_name(self) -> &'static str {
        match self {
            SmtSort::Int => "Int",
            SmtSort::Bool => "Bool",
            SmtSort::Real => "Real",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExactConstSymbol {
    name: String,
    sort: SmtSort,
}

/// A declared SMT-LIB variable with name, sort, and the original Lean expression.
///
/// The `lean_expr` field is used by `SmtSolver::Verifiable` to populate the
/// `VariableMapping` for proof reconstruction. Without it, the reconstruction
/// pipeline cannot translate ay term IDs back to kernel expressions. Part of #302.
#[derive(Debug, Clone)]
pub struct SmtVarDecl {
    pub name: String,
    pub sort: SmtSort,
    /// Original Lean expression that produced this SMT variable.
    /// Used to populate `VariableMapping` for proof reconstruction (#302).
    pub lean_expr: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RegisteredFVarKind {
    Scalar(SmtSort),
    Callable { result_sort: SmtSort },
}

#[derive(Debug, Clone)]
pub(super) struct RegisteredFVarDecl {
    pub name: String,
    pub kind: RegisteredFVarKind,
    pub lean_expr: Option<Expr>,
    pub lean_ty: Option<Expr>,
}

#[derive(Debug, Clone)]
#[cfg_attr(not(test), allow(dead_code))] // result_sort only read in tests (fvar_apps.rs)
pub struct SmtFuncDecl {
    pub name: String,
    pub domain_sorts: Vec<SmtSort>,
    pub result_sort: SmtSort,
    pub lean_expr: Expr,
    pub lean_ty: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TranslatedTerm {
    pub(super) smt: String,
    pub(super) sort: SmtSort,
}

/// Translator metadata for proof-producing existential Skolemization.
///
/// Fields are populated during translation and consumed by `ay_solver_translation.rs`
/// when the `ay-smt` feature is enabled. In test-only builds the struct is constructed
/// and checked for correct population but the individual fields are not read back.
#[derive(Debug, Clone)]
#[cfg_attr(not(feature = "ay-smt"), allow(dead_code))]
pub struct ExistsSkolemization {
    pub skolem_smt_name: String,
    pub binder_type: Expr,
    pub predicate: Expr,
    pub translator_placeholder_fvar: FVarId,
}

/// Base for internal existential-witness FVar placeholders.
///
/// Chosen to avoid collision with user FVarIds (small), MetaState FVarIds
/// (bit 63 set), and sentinel FVarIds (near `u64::MAX`). Part of #2848.
const SKOLEM_FVAR_BASE: u64 = 1_u64 << 62;

/// Translates clean kernel `Expr` values to SMT-LIB2 string format.
///
/// REQUIRES: None (pure translator, no preconditions on construction).
/// ENSURES: translate_expr returns valid SMT-LIB2 strings for the QF_LIA fragment.
///
/// Handles the QF_LIA subset: Nat/Int literals, Bool, arithmetic ops (+, -, *,
/// div, mod), comparisons (<, <=, >, >=, =, !=), and logical connectives
/// (and, or, not, =>).
pub struct SmtLibTranslator {
    /// Collected SMT-LIB declarations for variables
    pub(super) declarations: Vec<String>,
    /// Structured variable declarations (name + sort)
    pub(super) var_decls: Vec<SmtVarDecl>,
    /// Structured function declarations (name + signature + Lean metadata)
    pub(super) func_decls: Vec<SmtFuncDecl>,
    /// Registered FVars keyed by kernel id so translation can fail closed on
    /// unseen variables instead of inventing a default Int declaration.
    pub(super) registered_fvars: HashMap<FVarId, RegisteredFVarDecl>,
    /// Callable FVar heads that have already emitted a `(declare-fun ...)`.
    pub(super) fvar_func_decls: HashMap<FVarId, SmtFuncDecl>,
    /// Lean constant name → SMT-LIB symbol name + sort (deduplication).
    /// Without this, `Const("P")` appearing twice in `Or(P, Not(P))` would
    /// create two distinct SMT variables (P_0, P_1), making the formula
    /// satisfiable instead of a tautology. Part of #302.
    const_names: HashMap<String, ExactConstSymbol>,
    /// String literal value → SMT-LIB Int symbol (deduplication).
    /// Strings are outside the supported arithmetic fragments, so we lower
    /// them to stable opaque Int constants instead of conflating them to `0`.
    pub(super) string_constants: HashMap<String, String>,
    /// Existential Skolemization metadata accumulated across translations.
    pub(super) exists_skolemizations: Vec<ExistsSkolemization>,
    /// Counter for fresh variable names
    pub(super) fresh_counter: u32,
    /// Monotonic counter for internal existential-witness FVar placeholders.
    /// Starts at `SKOLEM_FVAR_BASE` to avoid collision with user FVarIds.
    /// Part of #2848.
    pub(super) next_internal_fvar: u64,
}

impl Default for SmtLibTranslator {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtLibTranslator {
    pub fn new() -> Self {
        SmtLibTranslator {
            declarations: Vec::new(),
            var_decls: Vec::new(),
            func_decls: Vec::new(),
            registered_fvars: HashMap::new(),
            fvar_func_decls: HashMap::new(),
            const_names: HashMap::new(),
            string_constants: HashMap::new(),
            exists_skolemizations: Vec::new(),
            fresh_counter: 0,
            next_internal_fvar: SKOLEM_FVAR_BASE,
        }
    }

    /// Return the canonical SMT symbol for a free variable.
    pub fn canonical_fvar_name(id: FVarId) -> String {
        format!("fvar_{}", id.as_u64())
    }
}

/// Extract a concrete Nat value from a literal expression.
///
/// Shared helper used by both the classifier-driven path (`classified.rs`)
/// and the atom boundary (`const_app.rs`).
pub(super) fn try_extract_concrete_nat(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract a concrete Int value from an Int constructor expression.
///
/// Shared helper used by both the classifier-driven path (`classified.rs`)
/// and the atom boundary (`const_app.rs`).
pub(super) fn try_extract_concrete_int(expr: &Expr) -> Option<i64> {
    if let ExprKind::Lit(Literal::Nat(n)) = expr.kind() {
        return n.to_u64().and_then(|v| i64::try_from(v).ok());
    }
    if let ExprKind::App(f, a) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            let name_str = name.to_string();
            match name_str.as_str() {
                "Int.ofNat" => {
                    return try_extract_concrete_nat(a).and_then(|n| i64::try_from(n).ok());
                }
                "Int.negSucc" => {
                    return try_extract_concrete_nat(a).and_then(|n| {
                        i64::try_from(n)
                            .ok()
                            .and_then(|n| n.checked_add(1).map(|v| -v))
                    });
                }
                _ => {}
            }
        }
    }
    None
}

#[cfg(test)]
mod tests;

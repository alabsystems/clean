// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Narrow cross-crate classifier contract for the proof-producing SMT translator.
//!
//! This module is the ONLY public classifier surface that `clean-elab` imports.
//! It wraps the internal `expr_classifier::LogicalForm` to keep bridge internals
//! (`Atom.original`, arithmetic `original` payloads, ematching state) out of the
//! cross-crate API.
//!
//! `clean-elab`'s `smt_translate` module calls [`classify_for_proof_translation`]
//! instead of maintaining its own semantic pattern-matching tables. This eliminates
//! the N-pipeline duplication that caused bugs #2808, #2809 (comparison/arithmetic
//! parity), and the broader structural drift tracked by #2806.
//!
//! Part of #2810.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::expr_classifier::{classify_expr, LogicalForm};

/// Public classifier result for the proof-producing SMT translation lane.
///
/// Intentionally narrower than the internal `LogicalForm`: omits native-lane-only
/// fields (e.g., `original` on arithmetic variants) to keep the cross-crate
/// surface auditable.
///
/// Part of #2810.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SmtLogicalForm {
    // --- Propositional ---
    Eq {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Neq {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    And(Expr, Expr),
    Or(Expr, Expr),
    Not(Expr),
    Implies(Expr, Expr),
    Iff(Expr, Expr),
    True,
    False,

    // --- Comparisons ---
    Lt {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Le {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Gt {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Ge {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },

    // --- Arithmetic ---
    // `ty` distinguishes Nat (monus/total semantics) from Int/Real (standard).
    Add {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Sub {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Mul {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Div {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Mod {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
    },
    Neg {
        ty: Expr,
        inner: Expr,
    },

    // --- Quantifiers ---
    Forall {
        binder_type: Expr,
        body: Expr,
    },
    /// Existential quantifier.
    ///
    /// The `body` field contains the lambda body with `BVar(0)` for the bound
    /// variable (extracted by the shared classifier). The `predicate` field
    /// preserves the raw second argument of the `Exists` application (typically
    /// a lambda) for proof reconstruction metadata. Downstream Skolemization
    /// records `predicate` in `ExistsSkolemization` so proof term validation
    /// can compare against the source proposition.
    Exists {
        binder_type: Expr,
        body: Expr,
        /// Raw predicate argument of the `Exists` application.
        predicate: Expr,
    },

    /// Opaque: not a recognized logical connective or arithmetic operator.
    Atom(Expr),
}

/// Classify a Lean expression for proof-producing SMT translation.
///
/// Delegates to the shared `expr_classifier::classify_expr` and converts the
/// internal `LogicalForm` to the public `SmtLogicalForm` wrapper.
///
/// For `Exists`, the raw predicate is recovered from the original expression
/// so downstream Skolemization metadata preserves structural equality with the
/// source proposition.
#[must_use]
pub fn classify_for_proof_translation(expr: &Expr) -> SmtLogicalForm {
    let internal = classify_expr(expr);
    match internal {
        // Int.negSucc is classified as Neg by the shared classifier, but it is
        // a constructor (-(n+1)), not standard negation (-(n)). The
        // proof-producing lane does not support it — return Atom to preserve
        // the current fail-closed behavior.
        LogicalForm::Neg { .. } => {
            let head = expr.strip_mdata().get_app_fn().strip_mdata();
            if let ExprKind::Const(name, _) = head.kind() {
                if *name == Name::from_string("Int.negSucc") {
                    return SmtLogicalForm::Atom(expr.strip_mdata().clone());
                }
            }
            from_internal(internal)
        }
        LogicalForm::Exists { binder_type, body } => {
            // Recover the raw predicate (second arg of Exists application) from
            // the original expression. The internal classifier already extracted
            // the lambda body, but proof reconstruction needs the original
            // predicate for structural equality checks in
            // `register_exists_witness_bindings`.
            let stripped = expr.strip_mdata();
            let raw_args = stripped.get_app_args();
            let predicate = if raw_args.len() >= 2 {
                raw_args[1].clone()
            } else {
                // Defensive fallback: reconstruct lambda from classifier output.
                // In practice, classify_expr only returns Exists for well-formed
                // `Exists(α, pred)` applications with 2 args.
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    binder_type.clone(),
                    body.clone(),
                )
            };
            SmtLogicalForm::Exists {
                binder_type,
                body,
                predicate,
            }
        }
        other => from_internal(other),
    }
}

/// Convert an internal `LogicalForm` to the public `SmtLogicalForm`.
///
/// Drops native-lane-only fields (`original` on arithmetic variants).
fn from_internal(form: LogicalForm) -> SmtLogicalForm {
    match form {
        LogicalForm::Eq { ty, lhs, rhs } => SmtLogicalForm::Eq { ty, lhs, rhs },
        LogicalForm::Neq { ty, lhs, rhs } => SmtLogicalForm::Neq { ty, lhs, rhs },
        LogicalForm::And(a, b) => SmtLogicalForm::And(a, b),
        LogicalForm::Or(a, b) => SmtLogicalForm::Or(a, b),
        LogicalForm::Not(a) => SmtLogicalForm::Not(a),
        LogicalForm::Implies(a, b) => SmtLogicalForm::Implies(a, b),
        LogicalForm::Iff(a, b) => SmtLogicalForm::Iff(a, b),
        LogicalForm::True => SmtLogicalForm::True,
        LogicalForm::False => SmtLogicalForm::False,
        LogicalForm::Lt { ty, lhs, rhs } => SmtLogicalForm::Lt { ty, lhs, rhs },
        LogicalForm::Le { ty, lhs, rhs } => SmtLogicalForm::Le { ty, lhs, rhs },
        LogicalForm::Gt { ty, lhs, rhs } => SmtLogicalForm::Gt { ty, lhs, rhs },
        LogicalForm::Ge { ty, lhs, rhs } => SmtLogicalForm::Ge { ty, lhs, rhs },
        LogicalForm::Add { ty, lhs, rhs, .. } => SmtLogicalForm::Add { ty, lhs, rhs },
        LogicalForm::Sub { ty, lhs, rhs, .. } => SmtLogicalForm::Sub { ty, lhs, rhs },
        LogicalForm::Mul { ty, lhs, rhs, .. } => SmtLogicalForm::Mul { ty, lhs, rhs },
        LogicalForm::Div { ty, lhs, rhs, .. } => SmtLogicalForm::Div { ty, lhs, rhs },
        LogicalForm::Mod { ty, lhs, rhs, .. } => SmtLogicalForm::Mod { ty, lhs, rhs },
        LogicalForm::Neg { ty, inner, .. } => SmtLogicalForm::Neg { ty, inner },
        LogicalForm::Forall { binder_type, body } => SmtLogicalForm::Forall { binder_type, body },
        // Exists handled specially in classify_for_proof_translation
        LogicalForm::Exists { binder_type, body } => SmtLogicalForm::Exists {
            binder_type: binder_type.clone(),
            body: body.clone(),
            predicate: Expr::lam(clean_kernel::BinderInfo::Default, binder_type, body),
        },
        LogicalForm::Atom(e) => SmtLogicalForm::Atom(e),
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared expression classifier for all SMT bridge translation pipelines.
//!
//! Provides a single `classify_expr()` function that classifies Lean kernel
//! expressions into canonical logical forms (`LogicalForm`). All three bridge
//! backends (SmtBridge, AyBackend, GoalClausifier) consume this classification
//! instead of independently pattern-matching on constant names.
//!
//! This eliminates the N-pipeline duplication that caused bugs #2261 (MData
//! not stripped), #2257 (missing Iff/Exists), #2255/#2260 (sort inference),
//! #2254 (monus bypass), and #2256 (Skolem for universal).
//!
//! Arithmetic variants (Add/Sub/Mul/Div/Mod/Neg) carry a `ty` field so
//! backends can dispatch on type-specific semantics (e.g., Nat.sub monus
//! vs Int.sub, Nat.div total vs Int.div).

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::bridge::name_match::name_eq_any;
// pub(super) so test submodules can access via `use super::*`
pub(super) use crate::bridge::name_match::name_eq_str;

/// Canonical logical form of a Lean expression.
///
/// Single source of truth for "what logical connective does this Lean
/// expression represent?" Backends convert `LogicalForm` to their specific
/// representation (TheoryLiteral, ay Term, NnfFormula).
///
/// Arithmetic variants carry a `ty` field so backends can dispatch on
/// type-specific semantics (Nat.sub monus vs Int.sub, Nat.div total vs
/// Int.div, Nat.mod total vs Int.mod).
#[derive(Debug, Clone)]
pub(crate) enum LogicalForm {
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
    // `ty` distinguishes Nat (total/monus semantics) from Int/Real (standard).
    // `original` preserves the original Lean expression for faithful reconstruction
    // by `logicalform_to_expr` without complex operator/instance rebuilding.
    // Fields are read by AyBackend::translate_arithmetic_form, which is behind
    // the `ay-smt` feature gate — invisible to clippy in default builds.
    #[allow(dead_code)]
    Add {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
        original: Expr,
    },
    #[allow(dead_code)]
    Sub {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
        original: Expr,
    },
    #[allow(dead_code)]
    Mul {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
        original: Expr,
    },
    #[allow(dead_code)]
    Div {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
        original: Expr,
    },
    #[allow(dead_code)]
    Mod {
        ty: Expr,
        lhs: Expr,
        rhs: Expr,
        original: Expr,
    },
    #[allow(dead_code)]
    Neg {
        ty: Expr,
        inner: Expr,
        original: Expr,
    },

    // --- Quantifiers ---
    Forall {
        binder_type: Expr,
        body: Expr,
    },
    Exists {
        binder_type: Expr,
        body: Expr,
    },

    /// Opaque: not a recognized logical connective or arithmetic operator.
    Atom(Expr),
}

/// Classify a Lean expression into its canonical logical form.
///
/// Strips MData transparently, classifies constant-head applications,
/// Pi types (non-dependent → Implies, dependent → Forall), and Exists.
pub(crate) fn classify_expr(expr: &Expr) -> LogicalForm {
    let expr = expr.strip_mdata();
    // Also strip MData from head — get_app_fn only peels App nodes,
    // so App(MData(_, Const("And")), x) returns MData(_, Const("And")) (#2261)
    let head = expr.get_app_fn().strip_mdata();
    let args = expr.get_app_args();

    match head.kind() {
        ExprKind::Const(name, _) => classify_const_app(name, &args, expr),
        ExprKind::Pi(_, domain, codomain) => {
            if codomain.has_loose_bvar(0) {
                LogicalForm::Forall {
                    binder_type: (**domain).clone(),
                    body: (**codomain).clone(),
                }
            } else {
                LogicalForm::Implies((**domain).clone(), (**codomain).clone())
            }
        }
        _ => LogicalForm::Atom(expr.clone()),
    }
}

fn classify_const_app(name: &Name, args: &[&Expr], expr: &Expr) -> LogicalForm {
    let n = args.len();
    // Eq/prop names use allocation-free Name matching.
    if let Some(form) = classify_eq_prop(name, n, args) {
        return form;
    }
    if let Some(form) = classify_comparison(name, n, args) {
        return form;
    }
    if let Some(form) = classify_arithmetic(name, n, args, expr) {
        return form;
    }
    // Exists: Exists α (λ x, body) — strip MData from predicate before checking Lam
    // If predicate is not a lambda (eta-contracted, e.g., `Exists Nat even`),
    // eta-expand: Exists α P → Exists α (λ x:α, P x), i.e., body = App(P, BVar(0))
    if name_eq_str(name, "Exists") && n == 2 {
        let pred = args[1].strip_mdata();
        match pred.kind() {
            ExprKind::Lam(_, _, body) => {
                return LogicalForm::Exists {
                    binder_type: args[0].clone(),
                    body: (**body).clone(),
                };
            }
            _ => {
                return LogicalForm::Exists {
                    binder_type: args[0].clone(),
                    body: Expr::app(pred.clone(), Expr::bvar(0)),
                };
            }
        }
    }
    LogicalForm::Atom(expr.clone())
}

fn classify_eq_prop(name: &Name, n: usize, args: &[&Expr]) -> Option<LogicalForm> {
    if n == 3 && name_eq_any(name, &["Eq", "eq"]) {
        return Some(LogicalForm::Eq {
            ty: args[0].clone(),
            lhs: args[1].clone(),
            rhs: args[2].clone(),
        });
    }
    if n >= 2 && name_eq_str(name, "BEq.beq") {
        return Some(LogicalForm::Eq {
            ty: if n >= 3 {
                args[0].clone()
            } else {
                Expr::const_(Name::from_string("Bool"), vec![])
            },
            lhs: args[n - 2].clone(),
            rhs: args[n - 1].clone(),
        });
    }
    if n == 3 && name_eq_any(name, &["Ne", "ne"]) {
        return Some(LogicalForm::Neq {
            ty: args[0].clone(),
            lhs: args[1].clone(),
            rhs: args[2].clone(),
        });
    }
    if n == 2 && name_eq_any(name, &["And", "and", "Bool.and"]) {
        return Some(LogicalForm::And(args[0].clone(), args[1].clone()));
    }
    if n == 2 && name_eq_any(name, &["Or", "or", "Bool.or"]) {
        return Some(LogicalForm::Or(args[0].clone(), args[1].clone()));
    }
    if n == 1 && name_eq_any(name, &["Not", "not", "Bool.not"]) {
        return Some(LogicalForm::Not(args[0].clone()));
    }
    if n == 2 && name_eq_str(name, "Iff") {
        return Some(LogicalForm::Iff(args[0].clone(), args[1].clone()));
    }
    if n == 0 && name_eq_str(name, "True") {
        return Some(LogicalForm::True);
    }
    if n == 0 && name_eq_str(name, "False") {
        return Some(LogicalForm::False);
    }
    None
}

/// Classify arithmetic comparison operators.
///
/// Delegates head-name classification to `head_family::classify_cmp_head`,
/// then resolves the type expression from arguments.
///
/// Lean 4 typeclass form: `@LT.lt.{u} {α : Type u} [inst : LT α] a b`
/// has ≥4 args: [type, instance, ..., lhs, rhs].
/// Direct form (`Int.lt`, `Nat.lt`, `Real.lt`) has 2 args: [lhs, rhs].
fn classify_comparison(name: &Name, n: usize, args: &[&Expr]) -> Option<LogicalForm> {
    use super::head_family::{classify_cmp_head_name, CmpFamily};

    if n < 2 {
        return None;
    }
    let head = classify_cmp_head_name(name)?;
    let type_hint = head.sort_hint.as_type_hint_str();

    // Resolve type: typeclass forms carry type in args[0], direct forms use name hint.
    // Bare 2-arg typeclass forms (e.g., LT.lt a b without type/instance) are partial
    // applications — don't classify them to avoid wrong default type (#2301).
    let ty = if n >= 4 {
        args[0].clone()
    } else if !type_hint.is_empty() {
        Expr::const_(Name::from_string(type_hint), vec![])
    } else {
        return None;
    };
    let lhs = args[n - 2].clone();
    let rhs = args[n - 1].clone();

    Some(match head.family {
        CmpFamily::Lt => LogicalForm::Lt { ty, lhs, rhs },
        CmpFamily::Le => LogicalForm::Le { ty, lhs, rhs },
        CmpFamily::Gt => LogicalForm::Gt { ty, lhs, rhs },
        CmpFamily::Ge => LogicalForm::Ge { ty, lhs, rhs },
    })
}

/// Resolve the type expression from type hint, argument count, and minimum arity
/// for the type to appear in args[0].
/// `min_typed_args` is 4 for binary ops (Op.op α inst lhs rhs), 3 for Neg (Neg.neg α inst inner).
/// Returns None for bare typeclass forms with insufficient args (#2301).
fn resolve_arithmetic_type(
    type_hint: &str,
    n: usize,
    args: &[&Expr],
    min_typed_args: usize,
) -> Option<Expr> {
    if n >= min_typed_args {
        Some(args[0].clone())
    } else if !type_hint.is_empty() {
        Some(Expr::const_(Name::from_string(type_hint), vec![]))
    } else {
        None
    }
}

/// Classify arithmetic operators.
///
/// Delegates head-name classification to `head_family::classify_arith_head`,
/// then resolves the type expression from arguments.
///
/// Lean 4 typeclass form: `@HAdd.hAdd.{u₁,u₂,u₃} {α} {β} {γ} [inst] a b`
/// has 6 args: [α, β, γ, inst, a, b]. Type is args[0].
/// Shorter typeclass form: `@Add.add {α} [inst] a b` has 4 args.
/// Direct form: `Nat.add a b` has 2 args.
fn classify_arithmetic(name: &Name, n: usize, args: &[&Expr], expr: &Expr) -> Option<LogicalForm> {
    use super::head_family::{classify_arith_head_name, ArithFamily};

    let head = classify_arith_head_name(name)?;
    let type_hint = head.sort_hint.as_type_hint_str();

    if head.is_unary() {
        if n < 1 {
            return None;
        }
    } else if n < 2 {
        return None;
    }

    // Binary ops: type appears at args[0] when n >= 4 (Op.op α inst lhs rhs)
    // Unary Neg: type appears at args[0] when n >= 3 (Neg.neg α inst inner)
    let min_typed_args = if head.is_unary() { 3 } else { 4 };
    let ty = resolve_arithmetic_type(type_hint, n, args, min_typed_args)?;
    let original = expr.clone();

    if head.is_unary() {
        return Some(LogicalForm::Neg {
            ty,
            inner: args[n - 1].clone(),
            original,
        });
    }

    let lhs = args[n - 2].clone();
    let rhs = args[n - 1].clone();

    Some(match head.family {
        ArithFamily::Add => LogicalForm::Add {
            ty,
            lhs,
            rhs,
            original,
        },
        ArithFamily::Sub => LogicalForm::Sub {
            ty,
            lhs,
            rhs,
            original,
        },
        ArithFamily::Mul => LogicalForm::Mul {
            ty,
            lhs,
            rhs,
            original,
        },
        ArithFamily::Div => LogicalForm::Div {
            ty,
            lhs,
            rhs,
            original,
        },
        ArithFamily::Mod => LogicalForm::Mod {
            ty,
            lhs,
            rhs,
            original,
        },
        ArithFamily::Neg => unreachable!("handled above"),
    })
}

/// Check if a constant name is a theory symbol recognized by the classifier.
///
/// Returns `true` for any name that `classify_expr` would recognize when
/// given the right number of arguments. Used by trigger extraction to filter
/// partial applications (where the head is a theory symbol but the argument
/// count doesn't match what `classify_expr` expects).
///
/// Also includes `HEq` which is a Lean 4 heterogeneous equality handled by
/// the equality theory but not yet modeled as a `LogicalForm` variant.
pub(crate) fn is_theory_const_name(name: &str) -> bool {
    // Equality/Propositional + special cases (not part of head_family)
    matches!(
        name,
        "Eq" | "eq"
            | "BEq.beq"
            | "Ne"
            | "ne"
            | "And"
            | "and"
            | "Bool.and"
            | "Or"
            | "or"
            | "Bool.or"
            | "Not"
            | "not"
            | "Bool.not"
            | "Iff"
            | "True"
            | "False"
            | "HEq"
            | "Exists"
    ) || super::head_family::is_arith_or_cmp_head(name)
}

#[cfg(test)]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper utilities for TLA+ tactics.
//!
//! This module provides common expression manipulation, pattern matching,
//! and proof state utilities used across different tactic implementations.
//!
//! The structural *destructors* (`extract_*`) live in the [`extract`]
//! submodule and are re-exported here, so callers keep importing them from
//! `crate::tactic::helpers`; this file keeps the predicates, the Pi-peeling
//! utilities, and the small expression constructors.

mod extract;

pub(crate) use extract::{extract_binary_arith, extract_equality, extract_succ};
pub use extract::{
    extract_comparison, extract_forall_nat, extract_implication, extract_nat_lit, extract_not,
    extract_or, extract_product_type, extract_tla_forall_in,
};

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

/// Peel off non-dependent Pi bindings to get the innermost goal.
pub fn peel_pis_to_innermost(expr: &Expr) -> Option<Expr> {
    let mut current = expr.clone();
    let mut peeled = false;

    while let ExprKind::Pi(_, _, body) = current.kind() {
        if !body.has_loose_bvars() {
            let next = (**body).clone();
            current = next;
            peeled = true;
        } else {
            break;
        }
    }

    if peeled {
        Some(current)
    } else {
        None
    }
}

/// Peel off hypothesis bindings and collect their types.
///
/// For a sequent-encoded goal like:
/// ```text
/// Pi(Implicit, TLA.Value,    -- declaration (skip)
///    Pi(Default, h1_type,    -- hypothesis (collect)
///       Pi(Default, h2_type, -- hypothesis (collect)
///          goal)))           -- inner goal
/// ```
///
/// This returns `([h1_type, h2_type], goal)`.
///
/// Key insight: Implicit Pis are declarations (constants, variables),
/// non-implicit non-dependent Pis are hypotheses (implications).
pub fn peel_hypotheses_with_context(expr: &Expr) -> (Vec<Expr>, Expr) {
    let mut current = expr.clone();
    let mut hypothesis_types = Vec::new();

    loop {
        match current.kind() {
            // Skip implicit declarations (constants, variables)
            // These are dependent Pis that introduce names used in the body
            ExprKind::Pi(bd, _, body) if bd.info == BinderInfo::Implicit => {
                let next = (**body).clone();
                current = next;
            }
            // Non-implicit, non-dependent Pi = hypothesis (implication)
            ExprKind::Pi(_, ty, body) if !body.has_loose_bvars() => {
                hypothesis_types.push((**ty).clone());
                let next = (**body).clone();
                current = next;
            }
            // Anything else: stop peeling
            _ => break,
        }
    }

    (hypothesis_types, current)
}

/// Wrap an expression with hypotheses as implications (Pi bindings).
///
/// Given hypotheses [h1, h2, ...] and a goal G, produces:
/// h1 → h2 → ... → G
///
/// This allows subgoals (like induction cases) to use the hypotheses
/// from the original obligation.
pub fn wrap_with_hypotheses(hypotheses: &[Expr], goal: Expr) -> Expr {
    let mut result = goal;
    for hyp in hypotheses.iter().rev() {
        result = Expr::pi(BinderInfo::Default, hyp.clone(), result);
    }
    result
}

/// Check if expression is trivially true (Bool.true, True constant, etc.)
pub fn is_trivially_true(expr: &Expr) -> bool {
    match expr.kind() {
        // Bool.true
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            name_str == "Bool.true" || name_str == "True" || name_str == "trivial"
        }
        // Application of True.intro or similar
        ExprKind::App(f, _) => {
            if let ExprKind::Const(name, _) = f.kind() {
                name.to_string() == "True.intro"
            } else {
                false
            }
        }
        // For pi-wrapped True, check innermost
        ExprKind::Pi(_, _, body) if !body.has_loose_bvars() => is_trivially_true(body),
        _ => false,
    }
}

/// Check if expression is trivially false (Bool.false or False)
pub fn is_trivially_false(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "Bool.false" || name_str == "False"
    } else {
        false
    }
}

/// Check if two expressions are structurally equal
pub fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    a == b
}

/// Check if an implication P → Q is trivially true.
///
/// An implication is trivially true if:
/// - Q is trivially true (True → True, P → True)
/// - P is trivially false (False → Q)
/// - P and Q are structurally equal (P → P)
pub fn is_implication_trivially_true(antecedent: &Expr, consequent: &Expr) -> bool {
    is_trivially_true(consequent)
        || is_trivially_false(antecedent)
        || exprs_equal(antecedent, consequent)
}

/// Check if expression is zero (Nat.zero, TLA.zero, Int 0, etc.)
pub fn is_zero(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            name_str == "Nat.zero" || name_str == "TLA.zero" || name_str == "Int.zero"
        }
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(0) => true,
        // Int.ofNat 0 or TLA.int 0
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Int.ofNat" || s == "TLA.int" {
                    return is_zero(arg);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is one (Nat.succ Nat.zero, etc.)
pub fn is_one(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(1) => true,
        // Nat.succ Nat.zero or Int.ofNat 1 or TLA.int 1
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return is_zero(arg);
                }
                if s == "Int.ofNat" || s == "TLA.int" {
                    return is_one(arg);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is 2 (in various forms)
pub fn is_two(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(2) => true,
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return is_one(arg);
                }
                if s == "Int.ofNat" || s == "TLA.int" {
                    return is_two(arg);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if type is Nat
pub fn is_nat_type(ty: &Expr) -> bool {
    if let ExprKind::Const(name, _) = ty.kind() {
        name.to_string() == "Nat"
    } else {
        false
    }
}

/// Check if expression represents the Nat set (TLA.Nat)
pub fn is_nat_set(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "TLA.Nat" || name_str == "Nat"
    } else {
        false
    }
}

/// Check if expression is Nat.succ(something)
pub fn is_succ_expr(expr: &Expr) -> bool {
    if let ExprKind::App(f, _) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            return name.to_string() == "Nat.succ";
        }
    }
    false
}

/// Check if expression is a positive constant (1, 2, 3, etc.)
pub fn is_positive_constant(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64().is_some_and(|v| v > 0),
        // Nat.succ anything is positive
        ExprKind::App(f, _) => {
            if let ExprKind::Const(name, _) = f.kind() {
                name.to_string() == "Nat.succ"
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if expression is n + k where k is a positive constant.
/// This is always > 0 for natural numbers since n >= 0.
pub fn is_add_positive(expr: &Expr) -> bool {
    // Pattern: App(App(TLA.add, n), k) where k is positive
    if let ExprKind::App(f, arg2) = expr.kind() {
        if let ExprKind::App(op, _arg1) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                if name.to_string() == "TLA.add" {
                    return is_positive_constant(arg2);
                }
            }
        }
    }
    false
}

/// Check if rhs is lhs + k where k is positive.
/// Returns true if rhs = lhs + k and k > 0.
pub fn is_expr_plus_positive(lhs: &Expr, rhs: &Expr) -> bool {
    // Pattern: rhs = App(App(TLA.add, lhs), k) where k > 0
    if let ExprKind::App(f, k) = rhs.kind() {
        if let ExprKind::App(op, arg) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                if name.to_string() == "TLA.add" && exprs_equal(arg, lhs) {
                    return is_positive_constant(k);
                }
            }
        }
    }
    false
}

/// Create a multiplication expression: a * b using TLA.mul
pub fn make_mul(a: &Expr, b: &Expr) -> Expr {
    let mul = Expr::const_(Name::from_string("TLA.mul"), vec![]);
    Expr::app(Expr::app(mul, a.clone()), b.clone())
}

/// Create an addition expression: a + b using TLA.add
pub fn make_add(a: &Expr, b: &Expr) -> Expr {
    let add = Expr::const_(Name::from_string("TLA.add"), vec![]);
    Expr::app(Expr::app(add, a.clone()), b.clone())
}

/// Debug string for an expression (for tracing)
pub(crate) fn expr_debug(expr: &Expr) -> String {
    match expr.kind() {
        ExprKind::Const(n, _) => format!("Const({})", n),
        ExprKind::BVar(i) => format!("BVar({})", i),
        ExprKind::Lit(l) => format!("Lit({:?})", l),
        ExprKind::App(f, a) => format!("App({}, {})", expr_debug(f), expr_debug(a)),
        ExprKind::Lam(_, ty, body) => format!("Lam({}, {})", expr_debug(ty), expr_debug(body)),
        ExprKind::Pi(_, ty, body) => format!("Pi({}, {})", expr_debug(ty), expr_debug(body)),
        _ => format!("{:?}", expr),
    }
}

/// Substitute occurrences of pattern with replacement in expr.
pub fn substitute(expr: &Expr, pattern: &Expr, replacement: &Expr) -> Expr {
    if exprs_equal(expr, pattern) {
        return replacement.clone();
    }

    match expr.kind() {
        ExprKind::App(f, a) => Expr::app(
            substitute(f, pattern, replacement),
            substitute(a, pattern, replacement),
        ),
        ExprKind::Lam(bi, ty, body) => Expr::lam(
            *bi,
            substitute(ty, pattern, replacement),
            substitute(body, pattern, replacement),
        ),
        ExprKind::Pi(bi, ty, body) => Expr::pi(
            *bi,
            substitute(ty, pattern, replacement),
            substitute(body, pattern, replacement),
        ),
        _ => expr.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_zero_variants() {
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        assert!(is_zero(&nat_zero));

        let lit_zero = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(0),
        )));
        assert!(is_zero(&lit_zero));

        let nat_one = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(1),
        )));
        assert!(!is_zero(&nat_one));
    }

    #[test]
    fn test_is_one_variants() {
        let lit_one = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(1),
        )));
        assert!(is_one(&lit_one));

        let succ_zero = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        assert!(is_one(&succ_zero));

        let lit_zero = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(0),
        )));
        assert!(!is_one(&lit_zero));
    }

    #[test]
    fn test_is_nat_set() {
        let tla_nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
        assert!(is_nat_set(&tla_nat));

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(is_nat_set(&nat));

        let other = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(!is_nat_set(&other));
    }

    #[test]
    fn test_peel_pis_to_innermost() {
        // Single non-dependent Pi: A -> B
        let b = Expr::const_(Name::from_string("B"), vec![]);
        let a = Expr::const_(Name::from_string("A"), vec![]);
        let impl_goal = Expr::pi(BinderInfo::Default, a.clone(), b.clone());

        let peeled = peel_pis_to_innermost(&impl_goal)
            .expect("peel_pis_to_innermost on A -> B should return innermost");
        assert_eq!(peeled, b);
    }

    #[test]
    fn test_extract_equality() {
        // TLA.eq lhs rhs
        let lhs = Expr::const_(Name::from_string("x"), vec![]);
        let rhs = Expr::const_(Name::from_string("y"), vec![]);
        let eq = Expr::const_(Name::from_string("TLA.eq"), vec![]);
        let eq_expr = Expr::app(Expr::app(eq, lhs.clone()), rhs.clone());

        let (l, r) = extract_equality(&eq_expr)
            .expect("extract_equality on TLA.eq x y should return (x, y)");
        assert_eq!(l, lhs);
        assert_eq!(r, rhs);
    }

    #[test]
    fn test_tla_int_pattern_matching() {
        // TLA.int 0 should be zero
        let tla_int_zero = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(0),
            ))),
        );
        assert!(is_zero(&tla_int_zero), "TLA.int 0 should be zero");

        // TLA.int 1 should be one
        let tla_int_one = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(1),
            ))),
        );
        assert!(is_one(&tla_int_one), "TLA.int 1 should be one");

        // TLA.int 2 should be two
        let tla_int_two = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(2),
            ))),
        );
        assert!(is_two(&tla_int_two), "TLA.int 2 should be two");

        // extract_nat_lit should work with TLA.int
        assert_eq!(extract_nat_lit(&tla_int_zero), Some(0));
        assert_eq!(extract_nat_lit(&tla_int_one), Some(1));
        assert_eq!(extract_nat_lit(&tla_int_two), Some(2));

        // TLA.int 42 should extract to 42
        let tla_int_42 = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(42),
            ))),
        );
        assert_eq!(extract_nat_lit(&tla_int_42), Some(42));
    }
}

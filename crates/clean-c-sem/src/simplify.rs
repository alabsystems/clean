// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic simplification of verification condition specifications.

use crate::expr::BinOp;
use crate::spec::Spec;

/// Whether reflexive comparison of this untyped specification term is known
/// to follow the source semantics.  `Spec::Var`, `Spec::Result`, and
/// `Spec::Expr` have lost their C type by this layer and may denote IEEE
/// floating values, for which `NaN == NaN`, `NaN <= NaN`, and `NaN >= NaN`
/// are false.  Keep the authoritative reflexivity lane closed unless the term
/// is built entirely from closed integer arithmetic.
pub(crate) fn reflexivity_is_authoritative(spec: &Spec) -> bool {
    match spec {
        Spec::Int(_) => true,
        Spec::BinOp {
            op: BinOp::Add | BinOp::Sub | BinOp::Mul,
            left,
            right,
        } => reflexivity_is_authoritative(left) && reflexivity_is_authoritative(right),
        Spec::UnaryOp {
            op: crate::expr::UnaryOp::Neg | crate::expr::UnaryOp::Pos,
            operand,
        } => reflexivity_is_authoritative(operand),
        _ => false,
    }
}

fn simplify_and(specs: &[Spec]) -> Spec {
    let simplified: Vec<_> = specs
        .iter()
        .map(simplify_spec)
        .filter(|s| !matches!(s, Spec::True))
        .collect();
    if simplified.is_empty() {
        Spec::True
    } else if simplified.iter().any(|s| matches!(s, Spec::False)) {
        Spec::False
    } else if simplified.len() == 1 {
        simplified
            .into_iter()
            .next()
            .expect("invariant: length checked")
    } else {
        Spec::And(simplified)
    }
}

fn simplify_or(specs: &[Spec]) -> Spec {
    let simplified: Vec<_> = specs
        .iter()
        .map(simplify_spec)
        .filter(|s| !matches!(s, Spec::False))
        .collect();
    if simplified.is_empty() {
        Spec::False
    } else if simplified.iter().any(|s| matches!(s, Spec::True)) {
        Spec::True
    } else if simplified.len() == 1 {
        simplified
            .into_iter()
            .next()
            .expect("invariant: length checked")
    } else {
        Spec::Or(simplified)
    }
}

fn simplify_not(inner: &Spec) -> Spec {
    let inner_simp = simplify_spec(inner);
    match inner_simp {
        Spec::True => Spec::False,
        Spec::False => Spec::True,
        Spec::Not(double_neg) => *double_neg,
        other => Spec::Not(Box::new(other)),
    }
}

fn simplify_implies(p: &Spec, q: &Spec) -> Spec {
    let p_simp = simplify_spec(p);
    let q_simp = simplify_spec(q);
    match (&p_simp, &q_simp) {
        (Spec::False, _) | (_, Spec::True) => Spec::True,
        (Spec::True, q) => q.clone(),
        _ => Spec::Implies(Box::new(p_simp), Box::new(q_simp)),
    }
}

fn simplify_binop(op: &BinOp, left: &Spec, right: &Spec) -> Spec {
    let left_simp = simplify_spec(left);
    let right_simp = simplify_spec(right);

    if left_simp == right_simp && reflexivity_is_authoritative(&left_simp) {
        match op {
            BinOp::Eq | BinOp::Le | BinOp::Ge => return Spec::True,
            BinOp::Ne | BinOp::Lt | BinOp::Gt => return Spec::False,
            _ => {}
        }
    }

    if let (Spec::Int(a), Spec::Int(b)) = (&left_simp, &right_simp) {
        if let Some(result) = fold_int_binop(op, *a, *b) {
            return result;
        }
    }

    Spec::BinOp {
        op: *op,
        left: Box::new(left_simp),
        right: Box::new(right_simp),
    }
}

fn fold_int_binop(op: &BinOp, a: i64, b: i64) -> Option<Spec> {
    Some(match op {
        BinOp::Eq => {
            if a == b {
                Spec::True
            } else {
                Spec::False
            }
        }
        BinOp::Ne => {
            if a != b {
                Spec::True
            } else {
                Spec::False
            }
        }
        BinOp::Lt => {
            if a < b {
                Spec::True
            } else {
                Spec::False
            }
        }
        BinOp::Le => {
            if a <= b {
                Spec::True
            } else {
                Spec::False
            }
        }
        BinOp::Gt => {
            if a > b {
                Spec::True
            } else {
                Spec::False
            }
        }
        BinOp::Ge => {
            if a >= b {
                Spec::True
            } else {
                Spec::False
            }
        }
        // Arithmetic folds use checked operations: on overflow we DECLINE to
        // fold (return None) rather than wrap or panic. Folding to a wrapped
        // constant would silently corrupt a verification condition, so the
        // sound choice is to leave the original `BinOp` un-simplified. This
        // mirrors the overflow-aware arithmetic in `CValue::add`/`CValue::sub`.
        BinOp::Add => Spec::Int(a.checked_add(b)?),
        BinOp::Sub => Spec::Int(a.checked_sub(b)?),
        BinOp::Mul => Spec::Int(a.checked_mul(b)?),
        _ => return None,
    })
}

/// Simplify a specification before proving.
/// Applies simple algebraic simplifications.
pub fn simplify_spec(spec: &Spec) -> Spec {
    match spec {
        Spec::And(specs) => simplify_and(specs),
        Spec::Or(specs) => simplify_or(specs),
        Spec::Not(inner) => simplify_not(inner),
        Spec::Implies(p, q) => simplify_implies(p, q),
        Spec::BinOp { op, left, right } => simplify_binop(op, left, right),
        _ => spec.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a `Spec::BinOp` over two integer literals.
    fn int_binop(op: BinOp, a: i64, b: i64) -> Spec {
        Spec::binop(op, Spec::int(a), Spec::int(b))
    }

    #[test]
    fn test_fold_add_small_values_simplifies() {
        let folded = simplify_spec(&int_binop(BinOp::Add, 2, 3));
        assert_eq!(folded, Spec::Int(5));
    }

    #[test]
    fn test_fold_sub_small_values_simplifies() {
        let folded = simplify_spec(&int_binop(BinOp::Sub, 10, 4));
        assert_eq!(folded, Spec::Int(6));
    }

    #[test]
    fn test_fold_mul_small_values_simplifies() {
        let folded = simplify_spec(&int_binop(BinOp::Mul, 6, 7));
        assert_eq!(folded, Spec::Int(42));
    }

    #[test]
    fn test_fold_add_overflow_declines() {
        // i64::MAX + 1 overflows: must leave the original BinOp un-folded,
        // never a wrapped Spec::Int.
        let original = int_binop(BinOp::Add, i64::MAX, 1);
        let folded = simplify_spec(&original);
        assert_eq!(folded, original);
        assert!(matches!(folded, Spec::BinOp { op: BinOp::Add, .. }));
    }

    #[test]
    fn test_fold_sub_overflow_declines() {
        // i64::MIN - 1 overflows: must decline to fold.
        let original = int_binop(BinOp::Sub, i64::MIN, 1);
        let folded = simplify_spec(&original);
        assert_eq!(folded, original);
        assert!(matches!(folded, Spec::BinOp { op: BinOp::Sub, .. }));
    }

    #[test]
    fn test_fold_mul_overflow_declines() {
        // i64::MAX * 2 overflows: must decline to fold.
        let original = int_binop(BinOp::Mul, i64::MAX, 2);
        let folded = simplify_spec(&original);
        assert_eq!(folded, original);
        assert!(matches!(folded, Spec::BinOp { op: BinOp::Mul, .. }));
    }
}

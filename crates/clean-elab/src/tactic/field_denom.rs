// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Field denominator operations: equality checking, common denominator
//! conversion, and denominator clearing via cross-multiplication.
//!
//! Split from `field.rs` per 500-line limit (#307).

use super::field::{
    field_add_terms, field_flatten_mul, field_mul_factors, field_negate, field_pow_expr, FieldExpr,
};
use super::ring_helpers::{ring_exprs_equal, ring_flatten_add, ring_flatten_mul, RingExpr};

pub(crate) fn field_has_denominator(expr: &FieldExpr) -> bool {
    match expr {
        FieldExpr::Div(_, _) | FieldExpr::Inv(_) => true,
        FieldExpr::Add(terms) | FieldExpr::Mul(terms) => terms.iter().any(field_has_denominator),
        FieldExpr::Pow(base, _) | FieldExpr::Neg(base) => field_has_denominator(base),
        FieldExpr::Const(_) | FieldExpr::Var(_) | FieldExpr::Unknown(_) => false,
    }
}

fn field_to_ring_expr(expr: &FieldExpr) -> RingExpr {
    match expr {
        FieldExpr::Const(n) => RingExpr::Const(*n),
        FieldExpr::Var(name) => RingExpr::Var(name.clone()),
        FieldExpr::Add(terms) => terms
            .iter()
            .map(field_to_ring_expr)
            .reduce(ring_flatten_add)
            .unwrap_or(RingExpr::Const(0)),
        FieldExpr::Mul(factors) => factors
            .iter()
            .map(field_to_ring_expr)
            .reduce(ring_flatten_mul)
            .unwrap_or(RingExpr::Const(1)),
        FieldExpr::Pow(base, exp) => {
            if *exp == 0 {
                RingExpr::Const(1)
            } else {
                RingExpr::Pow(Box::new(field_to_ring_expr(base)), *exp)
            }
        }
        FieldExpr::Neg(inner) => RingExpr::Neg(Box::new(field_to_ring_expr(inner))),
        FieldExpr::Div(_, _) | FieldExpr::Inv(_) => RingExpr::Unknown(format!("{expr:?}")),
        FieldExpr::Unknown(text) => RingExpr::Unknown(text.clone()),
    }
}

/// Check whether two normalized field expressions are equal after clearing denominators.
pub(crate) fn field_exprs_equal(a: &FieldExpr, b: &FieldExpr) -> bool {
    let (lhs, rhs) = clear_field_denominators(a, b);
    let lhs_ring = field_to_ring_expr(&lhs);
    let rhs_ring = field_to_ring_expr(&rhs);
    ring_exprs_equal(&lhs_ring, &rhs_ring)
}

/// Convert a field expression into a numerator/denominator pair.
pub(crate) fn to_common_denominator(expr: &FieldExpr) -> (FieldExpr, FieldExpr) {
    match expr {
        FieldExpr::Const(_) | FieldExpr::Var(_) | FieldExpr::Unknown(_) => {
            (expr.clone(), FieldExpr::Const(1))
        }
        FieldExpr::Neg(inner) => {
            let (numer, denom) = to_common_denominator(inner);
            (field_negate(numer), denom)
        }
        FieldExpr::Add(terms) => {
            let decomposed: Vec<_> = terms.iter().map(to_common_denominator).collect();
            let common_denom = decomposed
                .iter()
                .map(|(_, denom)| denom.clone())
                .reduce(field_flatten_mul)
                .unwrap_or(FieldExpr::Const(1));

            let numerators = decomposed
                .iter()
                .enumerate()
                .map(|(idx, (numer, _))| {
                    let other_denoms = decomposed
                        .iter()
                        .enumerate()
                        .filter(|(other_idx, _)| *other_idx != idx)
                        .map(|(_, (_, denom))| denom.clone())
                        .reduce(field_flatten_mul)
                        .unwrap_or(FieldExpr::Const(1));
                    field_flatten_mul(numer.clone(), other_denoms)
                })
                .collect();

            (field_add_terms(numerators), common_denom)
        }
        FieldExpr::Mul(factors) => {
            let decomposed: Vec<_> = factors.iter().map(to_common_denominator).collect();
            let numer = decomposed
                .iter()
                .map(|(numer, _)| numer.clone())
                .reduce(field_flatten_mul)
                .unwrap_or(FieldExpr::Const(1));
            let denom = decomposed
                .iter()
                .map(|(_, denom)| denom.clone())
                .reduce(field_flatten_mul)
                .unwrap_or(FieldExpr::Const(1));
            (numer, denom)
        }
        FieldExpr::Div(lhs, rhs) => {
            let (lhs_numer, lhs_denom) = to_common_denominator(lhs);
            let (rhs_numer, rhs_denom) = to_common_denominator(rhs);
            (
                field_mul_factors(vec![lhs_numer, rhs_denom]),
                field_mul_factors(vec![lhs_denom, rhs_numer]),
            )
        }
        FieldExpr::Inv(inner) => {
            let (numer, denom) = to_common_denominator(inner);
            (denom, numer)
        }
        FieldExpr::Pow(base, exp) => {
            let (numer, denom) = to_common_denominator(base);
            (field_pow_expr(numer, *exp), field_pow_expr(denom, *exp))
        }
    }
}

/// Clear all denominators from an equality.
pub(crate) fn clear_field_denominators(lhs: &FieldExpr, rhs: &FieldExpr) -> (FieldExpr, FieldExpr) {
    let (lhs_numer, lhs_denom) = to_common_denominator(lhs);
    let (rhs_numer, rhs_denom) = to_common_denominator(rhs);
    (
        field_mul_factors(vec![lhs_numer, rhs_denom]),
        field_mul_factors(vec![rhs_numer, lhs_denom]),
    )
}

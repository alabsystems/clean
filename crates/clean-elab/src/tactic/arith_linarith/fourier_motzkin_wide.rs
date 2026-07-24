// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified-only wide Fourier-Motzkin arithmetic.

use std::collections::{BTreeMap, BTreeSet};

use super::super::arithmetic::{LinearConstraint, LinearExpr};
use super::arena::{ArenaAllocator, ArenaLinearCombo};
use super::certificate::{CertifiedConstraint, FMCertifiedResult, LinarithCertificate};

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WideExprBackend {
    ArenaFlat,
    BTreeMap,
}

#[derive(Debug, Clone)]
struct BTreeLinearCombo {
    constant: i128,
    coeffs: BTreeMap<usize, i128>,
}

impl BTreeLinearCombo {
    fn constant(c: i128) -> Self {
        Self {
            constant: c,
            coeffs: BTreeMap::new(),
        }
    }

    fn from_linear_expr(expr: &LinearExpr) -> Self {
        Self {
            constant: i128::from(expr.constant),
            coeffs: expr
                .coeffs
                .iter()
                .map(|&(var, coeff)| (var, i128::from(coeff)))
                .collect(),
        }
    }

    fn scale(&self, factor: i128) -> Option<Self> {
        if factor == 0 {
            return Some(Self::constant(0));
        }

        let mut scaled = BTreeMap::new();
        for (&var, &coeff) in &self.coeffs {
            let new_coeff = coeff.checked_mul(factor)?;
            if new_coeff != 0 {
                scaled.insert(var, new_coeff);
            }
        }

        Some(Self {
            constant: self.constant.checked_mul(factor)?,
            coeffs: scaled,
        })
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut merged = self.coeffs.clone();
        for (&var, &coeff) in &other.coeffs {
            let entry = merged.entry(var).or_insert(0);
            *entry = entry.checked_add(coeff)?;
            if *entry == 0 {
                merged.remove(&var);
            }
        }

        Some(Self {
            constant: self.constant.checked_add(other.constant)?,
            coeffs: merged,
        })
    }

    fn without_var(&self, var: usize) -> Self {
        let mut coeffs = self.coeffs.clone();
        coeffs.remove(&var);
        Self {
            constant: self.constant,
            coeffs,
        }
    }

    fn coeff(&self, var: usize) -> i128 {
        *self.coeffs.get(&var).unwrap_or(&0)
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn extend_variables(&self, vars: &mut BTreeSet<usize>) {
        vars.extend(self.coeffs.keys().copied());
    }
}

#[derive(Debug, Clone)]
enum WideLinearExpr {
    Arena(ArenaLinearCombo),
    Map(BTreeLinearCombo),
}

impl WideLinearExpr {
    fn from_linear_expr(
        expr: &LinearExpr,
        backend: WideExprBackend,
        arena: &mut ArenaAllocator,
    ) -> Self {
        match backend {
            WideExprBackend::ArenaFlat => {
                Self::Arena(ArenaLinearCombo::from_linear_expr(expr, arena))
            }
            WideExprBackend::BTreeMap => Self::Map(BTreeLinearCombo::from_linear_expr(expr)),
        }
    }

    fn constant_value(&self) -> i128 {
        match self {
            Self::Arena(combo) => combo.constant,
            Self::Map(combo) => combo.constant,
        }
    }

    fn scale(&self, arena: &mut ArenaAllocator, factor: i128) -> Option<Self> {
        match self {
            Self::Arena(combo) => Some(Self::Arena(combo.scale(arena, factor)?)),
            Self::Map(combo) => Some(Self::Map(combo.scale(factor)?)),
        }
    }

    fn add(&self, other: &Self, arena: &mut ArenaAllocator) -> Option<Self> {
        match (self, other) {
            (Self::Arena(lhs), Self::Arena(rhs)) => Some(Self::Arena(lhs.add(rhs, arena)?)),
            (Self::Map(lhs), Self::Map(rhs)) => Some(Self::Map(lhs.add(rhs)?)),
            _ => unreachable!("wide expressions in one solver run must share a backend"),
        }
    }

    fn without_var(&self, arena: &mut ArenaAllocator, var: usize) -> Self {
        match self {
            Self::Arena(combo) => Self::Arena(combo.without_var(arena, var)),
            Self::Map(combo) => Self::Map(combo.without_var(var)),
        }
    }

    fn coeff(&self, arena: &ArenaAllocator, var: usize) -> i128 {
        match self {
            Self::Arena(combo) => combo.coeff(arena, var),
            Self::Map(combo) => combo.coeff(var),
        }
    }

    fn is_constant(&self) -> bool {
        match self {
            Self::Arena(combo) => combo.is_constant(),
            Self::Map(combo) => combo.is_constant(),
        }
    }

    fn extend_variables(&self, arena: &ArenaAllocator, vars: &mut BTreeSet<usize>) {
        match self {
            Self::Arena(combo) => combo.extend_variables(arena, vars),
            Self::Map(combo) => combo.extend_variables(vars),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum WideLinearConstraintKind {
    Le,
    Lt,
    Eq,
    Ne,
    Mod { modulus: i64 },
    NotMod { modulus: i64 },
}

#[derive(Debug, Clone)]
struct WideLinearConstraint {
    kind: WideLinearConstraintKind,
    expr: WideLinearExpr,
}

impl WideLinearConstraint {
    fn from_linear_constraint(
        constraint: &LinearConstraint,
        backend: WideExprBackend,
        arena: &mut ArenaAllocator,
    ) -> Self {
        match constraint {
            LinearConstraint::Le(expr) => Self {
                kind: WideLinearConstraintKind::Le,
                expr: WideLinearExpr::from_linear_expr(expr, backend, arena),
            },
            LinearConstraint::Lt(expr) => Self {
                kind: WideLinearConstraintKind::Lt,
                expr: WideLinearExpr::from_linear_expr(expr, backend, arena),
            },
            LinearConstraint::Eq(expr) => Self {
                kind: WideLinearConstraintKind::Eq,
                expr: WideLinearExpr::from_linear_expr(expr, backend, arena),
            },
            LinearConstraint::Ne(expr) => Self {
                kind: WideLinearConstraintKind::Ne,
                expr: WideLinearExpr::from_linear_expr(expr, backend, arena),
            },
            LinearConstraint::Mod { expr, modulus } => Self {
                kind: WideLinearConstraintKind::Mod { modulus: *modulus },
                expr: WideLinearExpr::from_linear_expr(expr, backend, arena),
            },
            LinearConstraint::NotMod { expr, modulus } => Self {
                kind: WideLinearConstraintKind::NotMod { modulus: *modulus },
                expr: WideLinearExpr::from_linear_expr(expr, backend, arena),
            },
        }
    }

    fn le(expr: WideLinearExpr) -> Self {
        Self {
            kind: WideLinearConstraintKind::Le,
            expr,
        }
    }

    fn lt(expr: WideLinearExpr) -> Self {
        Self {
            kind: WideLinearConstraintKind::Lt,
            expr,
        }
    }

    fn expr(&self) -> &WideLinearExpr {
        &self.expr
    }

    fn is_contradictory(&self) -> bool {
        let expr = self.expr();
        if !expr.is_constant() {
            return false;
        }
        match self.kind {
            WideLinearConstraintKind::Le => expr.constant_value() > 0,
            WideLinearConstraintKind::Lt => expr.constant_value() >= 0,
            WideLinearConstraintKind::Eq => expr.constant_value() != 0,
            WideLinearConstraintKind::Ne => expr.constant_value() == 0,
            WideLinearConstraintKind::Mod { modulus } => {
                expr.constant_value() % i128::from(modulus) != 0
            }
            WideLinearConstraintKind::NotMod { modulus } => {
                expr.constant_value() % i128::from(modulus) == 0
            }
        }
    }
}

#[derive(Debug, Clone)]
struct WideCertifiedConstraint {
    constraint: WideLinearConstraint,
    certificate: LinarithCertificate,
}

impl WideCertifiedConstraint {
    fn from_certified_constraint(
        constraint: &CertifiedConstraint,
        backend: WideExprBackend,
        arena: &mut ArenaAllocator,
    ) -> Self {
        Self {
            constraint: WideLinearConstraint::from_linear_constraint(
                &constraint.constraint,
                backend,
                arena,
            ),
            certificate: constraint.certificate.clone(),
        }
    }

    fn contradiction_evidence(&self) -> Option<Self> {
        if !self.constraint.is_contradictory() {
            return None;
        }

        let mut certificate = self.certificate.clone();
        let constant = self.constraint.expr().constant_value();
        certificate.result_constant = match self.constraint.kind {
            WideLinearConstraintKind::Lt => constant.max(1),
            _ => constant,
        };

        Some(Self {
            constraint: self.constraint.clone(),
            certificate,
        })
    }
}

struct WideFMBound<'a> {
    constraint: &'a WideCertifiedConstraint,
    rest: WideLinearExpr,
    coeff: i128,
    is_strict: bool,
}

fn is_wide_strict(constraint: &WideLinearConstraint) -> bool {
    matches!(constraint.kind, WideLinearConstraintKind::Lt)
}

fn wide_bound_coeff(coeff: i128) -> Option<i128> {
    coeff.checked_abs()
}

fn combine_wide_bounds(
    lower: &WideFMBound<'_>,
    upper: &WideFMBound<'_>,
    arena: &mut ArenaAllocator,
) -> Option<WideCertifiedConstraint> {
    let scaled_lower = lower.rest.scale(arena, upper.coeff)?;
    let scaled_upper = upper.rest.scale(arena, -lower.coeff)?;
    let new_expr = scaled_lower.add(&scaled_upper, arena)?;

    let scaled_lower_cert = lower.constraint.certificate.try_scale(upper.coeff)?;
    let scaled_upper_cert = upper.constraint.certificate.try_scale(lower.coeff)?;
    let certificate = scaled_lower_cert.try_add(&scaled_upper_cert)?;
    let constraint = if lower.is_strict || upper.is_strict {
        WideLinearConstraint::lt(new_expr)
    } else {
        WideLinearConstraint::le(new_expr)
    };

    Some(WideCertifiedConstraint {
        constraint,
        certificate,
    })
}

fn fourier_motzkin_eliminate_certified(
    constraints: &[WideCertifiedConstraint],
    var: usize,
    arena: &mut ArenaAllocator,
) -> Option<Vec<WideCertifiedConstraint>> {
    let mut lower_bounds: Vec<WideFMBound<'_>> = Vec::new();
    let mut upper_bounds: Vec<WideFMBound<'_>> = Vec::new();
    let mut no_var: Vec<WideCertifiedConstraint> = Vec::new();

    for constraint in constraints {
        let expr = constraint.constraint.expr();
        let coeff = expr.coeff(arena, var);

        if coeff == 0 {
            no_var.push(constraint.clone());
            continue;
        }

        let rest = expr.without_var(arena, var);
        let bound = WideFMBound {
            constraint,
            coeff: wide_bound_coeff(coeff)?,
            is_strict: is_wide_strict(&constraint.constraint),
            rest: if coeff > 0 {
                rest.scale(arena, -1)?
            } else {
                rest
            },
        };

        if coeff > 0 {
            upper_bounds.push(bound);
        } else {
            lower_bounds.push(bound);
        }
    }

    let mut result = no_var;
    for lower in &lower_bounds {
        for upper in &upper_bounds {
            result.push(combine_wide_bounds(lower, upper, arena)?);
        }
    }

    Some(result)
}

fn first_wide_contradiction(
    constraints: &[WideCertifiedConstraint],
) -> Option<WideCertifiedConstraint> {
    constraints
        .iter()
        .find_map(WideCertifiedConstraint::contradiction_evidence)
}

fn fourier_motzkin_check_certified_wide_with_backend(
    constraints: &[CertifiedConstraint],
    backend: WideExprBackend,
) -> FMCertifiedResult {
    if constraints.is_empty() {
        return FMCertifiedResult::Sat;
    }

    let mut arena = ArenaAllocator::default();
    let mut current: Vec<WideCertifiedConstraint> = constraints
        .iter()
        .map(|constraint| {
            WideCertifiedConstraint::from_certified_constraint(constraint, backend, &mut arena)
        })
        .collect();

    if let Some(contradiction) = first_wide_contradiction(&current) {
        return FMCertifiedResult::Unsat(contradiction.certificate);
    }

    let mut all_vars = BTreeSet::new();
    for constraint in &current {
        constraint
            .constraint
            .expr()
            .extend_variables(&arena, &mut all_vars);
    }

    for var in all_vars {
        let Some(next) = fourier_motzkin_eliminate_certified(&current, var, &mut arena) else {
            return FMCertifiedResult::Unknown;
        };
        current = next;

        if let Some(contradiction) = first_wide_contradiction(&current) {
            return FMCertifiedResult::Unsat(contradiction.certificate);
        }

        if current.len() > 1000 {
            return FMCertifiedResult::Unknown;
        }
    }

    if let Some(contradiction) = first_wide_contradiction(&current) {
        FMCertifiedResult::Unsat(contradiction.certificate)
    } else {
        FMCertifiedResult::Sat
    }
}

pub(super) fn fourier_motzkin_check_certified_wide(
    constraints: &[CertifiedConstraint],
) -> FMCertifiedResult {
    fourier_motzkin_check_certified_wide_with_backend(constraints, WideExprBackend::ArenaFlat)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expr_with_coeffs(constant: i64, coeffs: &[(usize, i64)]) -> LinearExpr {
        LinearExpr::from_coeffs(constant, coeffs.iter().copied())
    }

    #[test]
    fn test_linarith_certified_wide_arena_matches_btreemap_backend() {
        let mut lower = LinearExpr::var(0).scale(-1);
        lower.constant = 1;
        let upper = LinearExpr::var(0);
        let constraints = vec![
            CertifiedConstraint::from_hypothesis(LinearConstraint::Le(lower), 0, 2),
            CertifiedConstraint::from_hypothesis(LinearConstraint::Le(upper), 1, 2),
        ];

        let arena_result = fourier_motzkin_check_certified_wide_with_backend(
            &constraints,
            WideExprBackend::ArenaFlat,
        );
        let map_result = fourier_motzkin_check_certified_wide_with_backend(
            &constraints,
            WideExprBackend::BTreeMap,
        );

        match (arena_result, map_result) {
            (FMCertifiedResult::Unsat(arena_cert), FMCertifiedResult::Unsat(map_cert)) => {
                assert_eq!(arena_cert.coefficients, map_cert.coefficients);
                assert_eq!(arena_cert.result_constant, map_cert.result_constant);
            }
            (arena_other, map_other) => panic!(
                "expected both backends to derive the same contradiction, got arena={arena_other:?}, map={map_other:?}"
            ),
        }
    }

    #[test]
    fn test_linarith_certified_wide_arena_handles_large_coefficients() {
        let large = 4_000_000_000_i64;
        let mut lower = LinearExpr::var(0).scale(-large);
        lower.constant = large;
        let upper = LinearExpr::var(0).scale(large);

        let constraints = vec![
            CertifiedConstraint::from_hypothesis(LinearConstraint::Le(lower), 0, 2),
            CertifiedConstraint::from_hypothesis(LinearConstraint::Le(upper), 1, 2),
        ];

        match fourier_motzkin_check_certified_wide(&constraints) {
            FMCertifiedResult::Unsat(cert) => {
                let large_i128 = i128::from(large);
                assert_eq!(cert.coefficients, vec![large_i128, large_i128]);
                assert_eq!(cert.result_constant, large_i128 * large_i128);
                assert!(cert.is_valid(), "widened FM certificate must stay valid");
            }
            other => panic!(
                "expected widened certified FM to find the contradiction, got {:?}",
                other
            ),
        }
    }
}

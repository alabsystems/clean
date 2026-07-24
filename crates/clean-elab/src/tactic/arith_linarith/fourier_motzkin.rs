// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fourier-Motzkin variable elimination algorithms.
//!
//! Implements both uncertified and certified Fourier-Motzkin elimination
//! for checking satisfiability of linear constraint systems.

use std::collections::BTreeSet;

use super::super::arithmetic::{LinearConstraint, LinearExpr};
use super::certificate::{CertifiedConstraint, FMCertifiedResult, FMResult};
use super::fourier_motzkin_wide::fourier_motzkin_check_certified_wide;

#[derive(Debug)]
enum FMCheckResult<C> {
    Sat,
    Unsat(C),
    Unknown,
}

struct FMBound<'a, C> {
    constraint: &'a C,
    rest: LinearExpr,
    coeff: i64,
    is_strict: bool,
}

trait FMConstraint: Clone {
    fn constraint(&self) -> &LinearConstraint;

    fn contradiction_evidence(&self) -> Option<Self> {
        self.constraint().is_trivially_false().then(|| self.clone())
    }

    fn combine(lower: &FMBound<'_, Self>, upper: &FMBound<'_, Self>) -> Option<Self>;
}

impl FMConstraint for LinearConstraint {
    fn constraint(&self) -> &LinearConstraint {
        self
    }

    fn combine(lower: &FMBound<'_, Self>, upper: &FMBound<'_, Self>) -> Option<Self> {
        let new_expr = lower
            .rest
            .scale(upper.coeff)
            .sub(&upper.rest.scale(lower.coeff));
        Some(if lower.is_strict || upper.is_strict {
            LinearConstraint::Lt(new_expr)
        } else {
            LinearConstraint::Le(new_expr)
        })
    }
}

impl FMConstraint for CertifiedConstraint {
    fn constraint(&self) -> &LinearConstraint {
        &self.constraint
    }

    fn contradiction_evidence(&self) -> Option<Self> {
        if !self.constraint.is_trivially_false() {
            return None;
        }

        let mut certificate = self.certificate.clone();
        // For Le(c) where c > 0, result_constant = c > 0 satisfies is_valid().
        // For Lt(c) where c >= 0, result_constant = c may be 0 (the 0 < 0 case).
        // Use max(c, 1) for strict inequalities so the Farkas certificate is valid:
        // the contradiction is real (c >= 0 is not < 0), and result_constant > 0
        // preserves the is_valid() invariant without affecting proof reconstruction.
        let c = i128::from(self.constraint.expr().constant);
        certificate.result_constant = if matches!(self.constraint, LinearConstraint::Lt(_)) {
            c.max(1)
        } else {
            c
        };
        Some(Self {
            constraint: self.constraint.clone(),
            certificate,
        })
    }

    fn combine(lower: &FMBound<'_, Self>, upper: &FMBound<'_, Self>) -> Option<Self> {
        let scaled_lower = lower.rest.try_scale(upper.coeff)?;
        let scaled_upper = upper.rest.try_scale(lower.coeff)?;
        let new_expr = scaled_lower.try_sub(&scaled_upper)?;

        let scaled_lower_cert = lower
            .constraint
            .certificate
            .try_scale(i128::from(upper.coeff))?;
        let scaled_upper_cert = upper
            .constraint
            .certificate
            .try_scale(i128::from(lower.coeff))?;
        let certificate = scaled_lower_cert.try_add(&scaled_upper_cert)?;
        let constraint = if lower.is_strict || upper.is_strict {
            LinearConstraint::Lt(new_expr)
        } else {
            LinearConstraint::Le(new_expr)
        };

        Some(Self {
            constraint,
            certificate,
        })
    }
}

fn bound_coeff(coeff: i64) -> i64 {
    coeff.saturating_abs()
}

fn is_strict(constraint: &LinearConstraint) -> bool {
    matches!(constraint, LinearConstraint::Lt(_))
}

/// Perform Fourier-Motzkin variable elimination.
///
/// REQUIRES: `var` is a valid variable index
/// ENSURES: Result contains no constraints with non-zero coefficient for `var`
/// ENSURES: Each result constraint is a valid linear combination of inputs
/// ENSURES: If inputs are satisfiable, result is satisfiable (sound elimination)
fn fourier_motzkin_eliminate<C: FMConstraint>(constraints: &[C], var: usize) -> Vec<C> {
    let mut lower_bounds: Vec<FMBound<'_, C>> = Vec::new(); // var ≥ ...
    let mut upper_bounds: Vec<FMBound<'_, C>> = Vec::new(); // var ≤ ...
    let mut no_var: Vec<C> = Vec::new();

    for constraint in constraints {
        let expr = constraint.constraint().expr();
        let coeff = expr.get_coeff(var);

        if coeff == 0 {
            no_var.push(constraint.clone());
            continue;
        }

        let mut rest = expr.clone();
        rest.remove_var(var);
        let bound = FMBound {
            constraint,
            coeff: bound_coeff(coeff),
            is_strict: is_strict(constraint.constraint()),
            rest: if coeff > 0 { rest.scale(-1) } else { rest },
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
            if let Some(combined) = C::combine(lower, upper) {
                result.push(combined);
            }
        }
    }

    result
}

fn first_contradiction<C: FMConstraint>(constraints: &[C]) -> Option<C> {
    constraints
        .iter()
        .find_map(FMConstraint::contradiction_evidence)
}

fn fourier_motzkin_check_generic<C: FMConstraint>(constraints: &[C]) -> FMCheckResult<C> {
    if constraints.is_empty() {
        return FMCheckResult::Sat;
    }

    if let Some(contradiction) = first_contradiction(constraints) {
        return FMCheckResult::Unsat(contradiction);
    }

    let mut all_vars = BTreeSet::new();
    for constraint in constraints {
        all_vars.extend(constraint.constraint().expr().variables());
    }

    let mut current = constraints.to_vec();
    for var in all_vars {
        current = fourier_motzkin_eliminate(&current, var);

        if let Some(contradiction) = first_contradiction(&current) {
            return FMCheckResult::Unsat(contradiction);
        }

        if current.len() > 1000 {
            return FMCheckResult::Unknown;
        }
    }

    if let Some(contradiction) = first_contradiction(&current) {
        return FMCheckResult::Unsat(contradiction);
    }

    FMCheckResult::Sat
}

/// Run Fourier-Motzkin elimination to check satisfiability
///
/// REQUIRES: Each constraint in `constraints` is a valid `LinearConstraint`
/// ENSURES: `FMResult::Unsat` implies the system is truly unsatisfiable (soundness)
/// ENSURES: `FMResult::Sat` implies no contradiction was found (may be incomplete)
/// ENSURES: `FMResult::Unknown` when constraint count exceeds 1000 (growth limit)
/// ENSURES: Empty input returns `FMResult::Sat`
pub(crate) fn fourier_motzkin_check(constraints: &[LinearConstraint]) -> FMResult {
    match fourier_motzkin_check_generic(constraints) {
        FMCheckResult::Sat => FMResult::Sat,
        FMCheckResult::Unsat(_) => FMResult::Unsat,
        FMCheckResult::Unknown => FMResult::Unknown,
    }
}

/// Run certified Fourier-Motzkin elimination.
///
/// Returns a certificate if the constraints are unsatisfiable.
///
/// REQUIRES: Each `CertifiedConstraint` has a well-formed certificate
/// ENSURES: `Unsat(cert)` implies the system is truly unsatisfiable and `cert` is a valid Farkas witness
/// ENSURES: `Sat` implies no contradiction was found (may be incomplete)
/// ENSURES: `Unknown` when constraint count exceeds 1000 (growth limit)
/// ENSURES: Empty input returns `Sat`
pub(crate) fn fourier_motzkin_check_certified(
    constraints: &[CertifiedConstraint],
) -> FMCertifiedResult {
    fourier_motzkin_check_certified_wide(constraints)
}

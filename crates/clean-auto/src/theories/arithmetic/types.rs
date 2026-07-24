// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Types for the linear rational arithmetic theory solver.

use super::super::rational::{DeltaRational, Rational};
use crate::cdcl::Lit;
use std::collections::{BTreeMap, HashMap};

/// Variable identifier in the arithmetic theory
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArithVar(pub(crate) u32);

impl ArithVar {
    /// Create a new arithmetic variable from a raw index
    #[inline]
    pub fn new(raw: u32) -> Self {
        ArithVar(raw)
    }

    /// Get the raw variable index
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Type of bound
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoundType {
    /// x ≤ c
    Upper,
    /// x ≥ c
    Lower,
}

/// A bound on a variable with its justification literal.
///
/// Strictness is encoded in the `DeltaRational` value (#2334):
/// - `x <= b` uses value `(b, 0)`
/// - `x < b`  uses value `(b, -1)` meaning `b - epsilon`
/// - `x >= b` uses value `(b, 0)`
/// - `x > b`  uses value `(b, +1)` meaning `b + epsilon`
#[derive(Clone, Debug)]
pub struct Bound {
    pub(crate) value: DeltaRational,
    /// The literal that justified this bound
    pub(crate) reason: Lit,
    /// Decision level at which this bound was added
    pub(crate) level: u32,
}

impl Bound {
    #[inline]
    pub(crate) fn new(value: DeltaRational, reason: Lit, level: u32) -> Self {
        Self {
            value,
            reason,
            level,
        }
    }
}

/// Linear expression: Σ aᵢxᵢ
#[derive(Clone, Debug, Default)]
pub struct LinearExpr {
    /// Coefficients indexed by variable
    pub coeffs: BTreeMap<ArithVar, Rational>,
}

impl LinearExpr {
    pub fn new() -> Self {
        LinearExpr {
            coeffs: BTreeMap::new(),
        }
    }

    /// Add a term: expr += coeff * var. Returns None on overflow.
    pub fn add_term(&mut self, var: ArithVar, coeff: Rational) -> Option<()> {
        let entry = self.coeffs.entry(var).or_insert(Rational::ZERO);
        *entry = entry.add(&coeff)?;
        if entry.is_zero() {
            self.coeffs.remove(&var);
        }
        Some(())
    }
}

#[cfg(test)]
impl LinearExpr {
    /// Create expression with single variable coefficient (test-only, #2386).
    pub fn var(v: ArithVar) -> Self {
        let mut expr = LinearExpr::new();
        expr.coeffs.insert(v, Rational::ONE);
        expr
    }

    /// Multiply the entire expression by a scalar (test-only, #2386).
    pub fn scale(&mut self, scalar: &Rational) -> Option<()> {
        for coeff in self.coeffs.values_mut() {
            *coeff = coeff.mul(scalar)?;
        }
        Some(())
    }

    /// Add another expression: self += other (test-only, #2386).
    pub fn add_expr(&mut self, other: &LinearExpr) -> Option<()> {
        for (&var, coeff) in &other.coeffs {
            self.add_term(var, *coeff)?;
        }
        Some(())
    }

    /// Evaluate expression given variable assignments (test-only, #2386).
    pub fn evaluate(&self, assignment: &HashMap<ArithVar, Rational>) -> Option<Rational> {
        let mut sum = Rational::ZERO;
        for (&var, coeff) in &self.coeffs {
            if let Some(val) = assignment.get(&var) {
                sum = sum.add(&coeff.mul(val)?)?;
            }
        }
        Some(sum)
    }
}

/// Row in the simplex tableau
/// Represents: basic_var = constant + Σ coeffᵢ * non_basicᵢ
#[derive(Clone, Debug)]
pub(super) struct TableauRow {
    /// The basic variable for this row
    pub(super) basic_var: ArithVar,
    /// Constant term (plain Rational — tableau coefficients are exact)
    pub(super) constant: Rational,
    /// Coefficients for non-basic variables (plain Rational)
    pub(super) coeffs: BTreeMap<ArithVar, Rational>,
}

impl TableauRow {
    /// Evaluate the row given non-basic variable values (DeltaRational).
    /// Returns None on overflow.
    pub(super) fn evaluate(
        &self,
        assignment: &HashMap<ArithVar, DeltaRational>,
    ) -> Option<DeltaRational> {
        let mut sum = DeltaRational::from_rational(self.constant);
        for (&var, coeff) in &self.coeffs {
            if let Some(val) = assignment.get(&var) {
                sum = sum.add(&val.mul_rational(coeff)?)?;
            }
        }
        Some(sum)
    }
}

/// Statistics for arithmetic theory
#[derive(Clone, Debug, Default)]
pub struct ArithStats {
    pub num_vars: usize,
    pub num_rows: usize,
    pub num_lower_bounds: usize,
    pub num_upper_bounds: usize,
}

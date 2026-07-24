// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linarith proof certificate types.
//!
//! Tracks how linear inequalities are derived from original hypotheses
//! via Fourier-Motzkin elimination, enabling proof reconstruction.

use super::super::arithmetic::LinearConstraint;

/// A proof certificate for a linear arithmetic derivation.
///
/// This tracks how a linear inequality was derived from the original hypotheses
/// by recording which hypotheses were combined and with what coefficients.
/// The certificate can then be used to construct a kernel-valid proof term.
///
/// The key insight from Farkas' lemma is that if a system of linear inequalities
/// is infeasible, there exist non-negative coefficients c_i such that
/// Σ c_i * (constraint_i) yields a constant contradiction like 1 ≤ 0.
#[derive(Debug, Clone)]
pub struct LinarithCertificate {
    /// Coefficients for each original hypothesis, indexed by hypothesis position.
    /// A coefficient of 0 means the hypothesis wasn't used.
    pub coefficients: Vec<i128>,
    /// The resulting constant (should be > 0 for a valid certificate of unsatisfiability)
    pub result_constant: i128,
}

impl LinarithCertificate {
    /// Create an empty certificate
    ///
    /// REQUIRES: `num_hypotheses >= 0`
    /// ENSURES: `result.coefficients.len() == num_hypotheses`
    /// ENSURES: All coefficients are 0
    /// ENSURES: `result.result_constant == 0`
    pub fn new(num_hypotheses: usize) -> Self {
        Self {
            coefficients: vec![0_i128; num_hypotheses],
            result_constant: 0_i128,
        }
    }

    /// Create a certificate from a single hypothesis
    ///
    /// REQUIRES: `hyp_index < num_hypotheses`
    /// ENSURES: `result.coefficients[hyp_index] == 1`
    /// ENSURES: All other coefficients are 0
    /// ENSURES: `result.coefficients.len() == num_hypotheses`
    pub fn from_hypothesis(hyp_index: usize, num_hypotheses: usize) -> Self {
        let mut cert = Self::new(num_hypotheses);
        cert.coefficients[hyp_index] = 1;
        cert
    }

    /// Scale the certificate by a positive factor.
    ///
    /// Uses saturating arithmetic. For certified paths that need overflow
    /// detection, use [`try_scale`](Self::try_scale).
    ///
    /// REQUIRES: `factor >= 0` for sound certificates
    /// ENSURES: `result.coefficients[i] == self.coefficients[i] *_sat factor` for all `i`
    /// ENSURES: `result.result_constant == self.result_constant *_sat factor`
    /// ENSURES: `result.coefficients.len() == self.coefficients.len()`
    #[must_use]
    pub fn scale(&self, factor: i128) -> Self {
        Self {
            coefficients: self
                .coefficients
                .iter()
                .map(|&c| c.saturating_mul(factor))
                .collect(),
            result_constant: self.result_constant.saturating_mul(factor),
        }
    }

    /// Scale the certificate by a positive factor, returning `None` on overflow.
    ///
    /// Used in certified Fourier-Motzkin where silent wrapping would produce
    /// incorrect Farkas certificates and potentially unsound proofs.
    ///
    /// REQUIRES: `factor >= 0` for sound certificates
    /// ENSURES: On `Some(result)`, `result.coefficients[i] == self.coefficients[i] * factor` exactly (no overflow)
    /// ENSURES: On `None`, at least one multiplication overflowed `i128`
    pub fn try_scale(&self, factor: i128) -> Option<Self> {
        let coefficients: Option<Vec<i128>> = self
            .coefficients
            .iter()
            .map(|&c| c.checked_mul(factor))
            .collect();
        Some(Self {
            coefficients: coefficients?,
            result_constant: self.result_constant.checked_mul(factor)?,
        })
    }

    /// Add two certificates (for combining constraints).
    ///
    /// Uses saturating arithmetic. For certified paths that need overflow
    /// detection, use [`try_add`](Self::try_add).
    ///
    /// REQUIRES: `self.coefficients.len() == other.coefficients.len()`
    /// ENSURES: `result.coefficients[i] == self.coefficients[i] +_sat other.coefficients[i]` for all `i`
    /// ENSURES: `result.result_constant == self.result_constant +_sat other.result_constant`
    /// ENSURES: Panics if coefficient vector lengths differ
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(
            self.coefficients.len(),
            other.coefficients.len(),
            "certificates must have same number of hypotheses"
        );
        Self {
            coefficients: self
                .coefficients
                .iter()
                .zip(&other.coefficients)
                .map(|(&a, &b)| a.saturating_add(b))
                .collect(),
            result_constant: self.result_constant.saturating_add(other.result_constant),
        }
    }

    /// Add two certificates, returning `None` on overflow.
    ///
    /// REQUIRES: `self.coefficients.len() == other.coefficients.len()`
    /// ENSURES: On `Some(result)`, all additions are exact (no overflow)
    /// ENSURES: On `None`, at least one addition overflowed or lengths differ
    pub fn try_add(&self, other: &Self) -> Option<Self> {
        if self.coefficients.len() != other.coefficients.len() {
            return None;
        }
        let coefficients: Option<Vec<i128>> = self
            .coefficients
            .iter()
            .zip(&other.coefficients)
            .map(|(&a, &b)| a.checked_add(b))
            .collect();
        Some(Self {
            coefficients: coefficients?,
            result_constant: self.result_constant.checked_add(other.result_constant)?,
        })
    }

    /// Check if all coefficients are non-negative (required for validity)
    ///
    /// ENSURES: Returns `true` iff all coefficients >= 0 AND `result_constant > 0`
    /// ENSURES: A valid certificate represents a Farkas witness for unsatisfiability
    pub fn is_valid(&self) -> bool {
        self.coefficients.iter().all(|&c| c >= 0) && self.result_constant > 0
    }
}

/// A linear constraint with its proof certificate
#[derive(Debug, Clone)]
pub struct CertifiedConstraint {
    /// The constraint
    pub constraint: LinearConstraint,
    /// The certificate tracking which original hypotheses contribute to this constraint
    pub certificate: LinarithCertificate,
}

impl CertifiedConstraint {
    /// Create a certified constraint from an original hypothesis
    ///
    /// REQUIRES: `hyp_index < num_hypotheses`
    /// ENSURES: `result.certificate.coefficients[hyp_index] == 1`
    /// ENSURES: `result.constraint` is `constraint` unchanged
    pub fn from_hypothesis(
        constraint: LinearConstraint,
        hyp_index: usize,
        num_hypotheses: usize,
    ) -> Self {
        Self {
            constraint,
            certificate: LinarithCertificate::from_hypothesis(hyp_index, num_hypotheses),
        }
    }

    /// Create a certified constraint from the negated goal
    ///
    /// REQUIRES: `constraint` is the negation of the goal constraint
    /// ENSURES: `result.certificate.coefficients.len() == num_hypotheses + 1`
    /// ENSURES: `result.certificate.coefficients[num_hypotheses] == 1` (goal slot)
    pub fn from_negated_goal(constraint: LinearConstraint, num_hypotheses: usize) -> Self {
        // The negated goal is treated as hypothesis index = num_hypotheses
        Self {
            constraint,
            certificate: LinarithCertificate::from_hypothesis(num_hypotheses, num_hypotheses + 1),
        }
    }
}

/// Result of Fourier-Motzkin with proof certificate
#[derive(Debug)]
pub enum FMCertifiedResult {
    /// Constraints are satisfiable
    Sat,
    /// Constraints are unsatisfiable with a certificate
    Unsat(LinarithCertificate),
    /// Could not determine (incomplete)
    Unknown,
}

/// Fourier-Motzkin elimination result
#[derive(Debug)]
pub enum FMResult {
    /// Constraints are satisfiable
    Sat,
    /// Constraints are unsatisfiable (contradiction found)
    Unsat,
    /// Could not determine (incomplete)
    Unknown,
}

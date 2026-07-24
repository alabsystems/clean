// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cutting Planes Proof System
//!
//! Operates over pseudo-Boolean (0/1 integer linear) inequalities of the form:
//!   a_1*x_1 + a_2*x_2 + ... + a_n*x_n >= b
//!
//! Rules:
//! - **Addition**: add two inequalities coefficient-wise.
//! - **Multiplication**: multiply an inequality by a positive integer.
//! - **Division**: divide by a positive integer (ceiling on RHS).
//! - **Saturation**: cap coefficients at the RHS value (valid for 0/1 variables).
//!
//! Cutting Planes is strictly stronger than resolution (Cook, Coullard, Turan 1987):
//! PHP has polynomial-size CP proofs but requires exponential resolution proofs.

use serde::{Deserialize, Serialize};

/// A pseudo-Boolean inequality: sum(coeffs[i] * x_i) >= rhs, where x_i in {0,1}.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CpInequality {
    /// Coefficients indexed by variable (0-indexed).
    pub coeffs: Vec<i64>,
    /// Right-hand side.
    pub rhs: i64,
}

impl CpInequality {
    #[must_use]
    pub fn new(coeffs: Vec<i64>, rhs: i64) -> Self {
        Self { coeffs, rhs }
    }

    /// Evaluate the inequality under a 0/1 assignment. Returns true if satisfied.
    #[must_use]
    pub fn evaluate(&self, assignment: &[bool]) -> bool {
        let sum: i64 = self
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, &c)| {
                if assignment.get(i).copied().unwrap_or(false) {
                    c
                } else {
                    0
                }
            })
            .sum();
        sum >= self.rhs
    }

    /// Check if this inequality is trivially valid (all coefficients non-negative
    /// and sum >= rhs, or rhs <= 0).
    #[must_use]
    pub fn is_trivially_valid(&self) -> bool {
        if self.rhs <= 0 {
            return true;
        }
        self.coeffs.iter().all(|&c| c >= 0) && self.coeffs.iter().sum::<i64>() >= self.rhs
    }
}

/// A step in a cutting planes proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpStep {
    /// Introduce an input inequality (axiom).
    Input(CpInequality),
    /// Add two inequalities (by index).
    Add(usize, usize),
    /// Multiply an inequality by a positive scalar.
    Multiply(usize, i64),
    /// Divide an inequality by a positive integer (ceiling on RHS).
    Divide(usize, i64),
    /// Saturate: cap each coefficient at the RHS value.
    Saturate(usize),
}

/// A cutting planes proof: a sequence of derivation steps.
#[derive(Debug, Clone)]
pub struct CuttingPlanesProof {
    steps: Vec<CpStep>,
    derived: Vec<CpInequality>,
}

impl CuttingPlanesProof {
    #[must_use]
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            derived: Vec::new(),
        }
    }

    /// Add an input inequality. Returns its step index.
    pub fn add_input(&mut self, ineq: CpInequality) -> usize {
        let idx = self.steps.len();
        self.derived.push(ineq.clone());
        self.steps.push(CpStep::Input(ineq));
        idx
    }

    /// Add two inequalities. Returns the new step index.
    pub fn add(&mut self, left: usize, right: usize) -> Result<usize, String> {
        let (l, r) = self.get_pair(left, right)?;
        let n = l.coeffs.len().max(r.coeffs.len());
        let mut coeffs = vec![0i64; n];
        for (i, c) in coeffs.iter_mut().enumerate() {
            *c = l.coeffs.get(i).copied().unwrap_or(0) + r.coeffs.get(i).copied().unwrap_or(0);
        }
        let rhs = l.rhs + r.rhs;
        let ineq = CpInequality::new(coeffs, rhs);
        let idx = self.steps.len();
        self.derived.push(ineq);
        self.steps.push(CpStep::Add(left, right));
        Ok(idx)
    }

    /// Multiply an inequality by a positive scalar.
    pub fn multiply(&mut self, step: usize, scalar: i64) -> Result<usize, String> {
        if scalar <= 0 {
            return Err(format!("scalar must be positive, got {scalar}"));
        }
        let base = self.get_one(step)?;
        let coeffs: Vec<i64> = base.coeffs.iter().map(|&c| c * scalar).collect();
        let rhs = base.rhs * scalar;
        let ineq = CpInequality::new(coeffs, rhs);
        let idx = self.steps.len();
        self.derived.push(ineq);
        self.steps.push(CpStep::Multiply(step, scalar));
        Ok(idx)
    }

    /// Divide an inequality by a positive integer (ceiling on RHS).
    pub fn divide(&mut self, step: usize, divisor: i64) -> Result<usize, String> {
        if divisor <= 0 {
            return Err(format!("divisor must be positive, got {divisor}"));
        }
        let base = self.get_one(step)?;
        let coeffs: Vec<i64> = base.coeffs.iter().map(|&c| div_ceil(c, divisor)).collect();
        let rhs = div_ceil(base.rhs, divisor);
        let ineq = CpInequality::new(coeffs, rhs);
        let idx = self.steps.len();
        self.derived.push(ineq);
        self.steps.push(CpStep::Divide(step, divisor));
        Ok(idx)
    }

    /// Saturate: cap each coefficient at the RHS value (valid for 0/1 variables).
    pub fn saturate(&mut self, step: usize) -> Result<usize, String> {
        let base = self.get_one(step)?;
        let rhs = base.rhs;
        let coeffs: Vec<i64> = base.coeffs.iter().map(|&c| c.min(rhs).max(0)).collect();
        let ineq = CpInequality::new(coeffs, rhs);
        let idx = self.steps.len();
        self.derived.push(ineq);
        self.steps.push(CpStep::Saturate(step));
        Ok(idx)
    }

    /// Get the derived inequality at a step index.
    #[must_use]
    pub fn inequality_at(&self, idx: usize) -> Option<&CpInequality> {
        self.derived.get(idx)
    }

    /// Get the proof step at an index.
    #[must_use]
    pub fn step_at(&self, idx: usize) -> Option<&CpStep> {
        self.steps.get(idx)
    }

    /// Number of steps.
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the proof is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Verify the proof derives a contradiction: 0 >= c for c > 0.
    #[must_use]
    pub fn verify(&self) -> bool {
        self.derived
            .last()
            .is_some_and(|ineq| ineq.coeffs.iter().all(|&c| c == 0) && ineq.rhs > 0)
    }

    /// Verify that the proof derives a contradiction from the given
    /// source inequalities only.
    ///
    /// SOUNDNESS FIX (#3331): This checks that every `Input` step matches
    /// an inequality in the provided source formula. Without this check,
    /// a proof could introduce arbitrary axiom inequalities not present in
    /// the original formula and derive a false refutation.
    #[must_use]
    pub fn verify_against_formula(&self, formula_inequalities: &[CpInequality]) -> bool {
        for (i, step) in self.steps.iter().enumerate() {
            if let CpStep::Input(ineq) = step {
                let found = formula_inequalities.iter().any(|fi| fi == ineq);
                if !found {
                    // Input inequality at step {i} not in source formula.
                    let _ = i; // suppress unused warning
                    return false;
                }
            }
        }
        self.verify()
    }

    fn get_one(&self, idx: usize) -> Result<CpInequality, String> {
        self.derived
            .get(idx)
            .cloned()
            .ok_or_else(|| format!("invalid step index: {idx}"))
    }

    fn get_pair(&self, l: usize, r: usize) -> Result<(CpInequality, CpInequality), String> {
        Ok((self.get_one(l)?, self.get_one(r)?))
    }
}

impl Default for CuttingPlanesProof {
    fn default() -> Self {
        Self::new()
    }
}

/// Integer division rounding toward positive infinity.
fn div_ceil(a: i64, b: i64) -> i64 {
    assert!(b > 0);
    if a >= 0 {
        (a + b - 1) / b
    } else {
        a / b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cp_inequality_evaluate() {
        let ineq = CpInequality::new(vec![1, 2, 3], 3);
        assert!(ineq.evaluate(&[false, true, true])); // 0 + 2 + 3 = 5 >= 3
        assert!(!ineq.evaluate(&[true, false, false])); // 1 + 0 + 0 = 1 < 3
    }

    #[test]
    fn test_cp_add() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1, 0], 1));
        let b = proof.add_input(CpInequality::new(vec![0, 1], 1));
        let c = proof.add(a, b).expect("add");
        let ineq = proof.inequality_at(c).expect("get");
        assert_eq!(ineq.coeffs, vec![1, 1]);
        assert_eq!(ineq.rhs, 2);
    }

    #[test]
    fn test_cp_multiply() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1, 2], 3));
        let b = proof.multiply(a, 2).expect("multiply");
        let ineq = proof.inequality_at(b).expect("get");
        assert_eq!(ineq.coeffs, vec![2, 4]);
        assert_eq!(ineq.rhs, 6);
    }

    #[test]
    fn test_cp_divide_ceiling() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![2, 3], 5));
        let b = proof.divide(a, 2).expect("divide");
        let ineq = proof.inequality_at(b).expect("get");
        assert_eq!(ineq.coeffs, vec![1, 2]); // ceil(2/2)=1, ceil(3/2)=2
        assert_eq!(ineq.rhs, 3); // ceil(5/2) = 3
    }

    #[test]
    fn test_cp_saturate() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![5, 3, 1], 3));
        let b = proof.saturate(a).expect("saturate");
        let ineq = proof.inequality_at(b).expect("get");
        assert_eq!(ineq.coeffs, vec![3, 3, 1]); // 5 capped at 3
        assert_eq!(ineq.rhs, 3);
    }

    #[test]
    fn test_cp_multiply_nonpositive_fails() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        assert!(proof.multiply(a, 0).is_err());
        assert!(proof.multiply(a, -1).is_err());
    }

    #[test]
    fn test_cp_trivially_valid() {
        assert!(CpInequality::new(vec![1, 2], 0).is_trivially_valid());
        assert!(CpInequality::new(vec![1, 2], -1).is_trivially_valid());
        assert!(CpInequality::new(vec![1, 2], 3).is_trivially_valid());
        assert!(!CpInequality::new(vec![1, 2], 4).is_trivially_valid());
    }

    #[test]
    fn test_cp_proof_verify_contradiction() {
        let mut proof = CuttingPlanesProof::new();
        // x >= 1 and -x >= 0 => add => 0 >= 1 (contradiction)
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        let b = proof.add_input(CpInequality::new(vec![-1], 0));
        let c = proof.add(a, b).expect("add");
        let ineq = proof.inequality_at(c).expect("get");
        assert_eq!(ineq.coeffs, vec![0]);
        assert_eq!(ineq.rhs, 1);
        assert!(proof.verify());
    }

    // ---- #3331: Formula binding verification ----

    #[test]
    fn test_cp_verify_against_formula_valid() {
        let formula = vec![
            CpInequality::new(vec![1], 1),
            CpInequality::new(vec![-1], 0),
        ];
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        let b = proof.add_input(CpInequality::new(vec![-1], 0));
        proof.add(a, b).expect("add");
        assert!(proof.verify_against_formula(&formula));
    }

    #[test]
    fn test_cp_verify_against_formula_rejects_foreign_input() {
        // Formula only has x >= 1. Proof introduces -x >= 0 which is foreign.
        let formula = vec![CpInequality::new(vec![1], 1)];
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        let b = proof.add_input(CpInequality::new(vec![-1], 0)); // foreign
        proof.add(a, b).expect("add");
        assert!(!proof.verify_against_formula(&formula));
    }
}

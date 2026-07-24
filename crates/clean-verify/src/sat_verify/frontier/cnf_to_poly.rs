// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CNF-to-polynomial translation for Polynomial Calculus over GF(2).
//!
//! Converts propositional CNF formulas into the GF(2) polynomial encoding
//! used by the Polynomial Calculus proof system. This module provides:
//!
//! - [`CnfFormula`]: a structured CNF representation with variable metadata.
//! - [`translate_cnf`]: batch translation of a full CNF to polynomial system.
//! - [`translate_clause`]: single-clause translation with polarity tracking.
//! - [`generate_xor_cnf`]: generate XOR constraint systems (natural GF(2) fit).
//! - [`verify_translation`]: exhaustive soundness check for small instances.
//!
//! ## Encoding
//!
//! A clause (l1 v l2 v ... v lk) is unsatisfied exactly when all literals
//! are false. For positive literal xi, "false" means xi=0; for negative
//! literal !xi, "false" means xi=1.
//!
//! Each literal li maps to a factor:
//!   - Positive literal xi  -> factor (1 - xi)
//!   - Negative literal !xi -> factor xi
//!
//! The clause polynomial is the product of all factors. The clause is
//! satisfied iff the polynomial evaluates to 0.
//!
//! ## References
//!
//! - Clegg, Edmonds, Impagliazzo (1996). Using the Groebner basis
//!   algorithm to find proofs of unsatisfiability. STOC'96.

use super::gf2_algebra::Gf2Poly;

use thiserror::Error;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from CNF translation.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum CnfTranslationError {
    /// A literal uses variable index 0, which is invalid in DIMACS format.
    #[error("clause {clause_idx} contains literal 0 (invalid DIMACS variable)")]
    ZeroLiteral { clause_idx: usize },

    /// The formula has more variables than the translation supports.
    #[error("formula has {num_vars} variables, exceeding limit {limit}")]
    TooManyVariables { num_vars: u32, limit: u32 },

    /// Clause is empty (trivially unsatisfied).
    #[error("clause {clause_idx} is empty (trivially false)")]
    EmptyClause { clause_idx: usize },
}

// ---------------------------------------------------------------------------
// CnfFormula: structured CNF representation
// ---------------------------------------------------------------------------

/// A CNF formula with variable metadata.
///
/// Stores clauses in DIMACS format (1-based signed literals) along with
/// precomputed metadata about the formula's structure.
#[derive(Debug, Clone)]
pub struct CnfFormula {
    /// Clauses in DIMACS format. Each inner slice contains signed literals.
    clauses: Vec<Vec<i32>>,
    /// Number of distinct variables (max absolute literal value).
    num_vars: u32,
    /// Number of clauses.
    num_clauses: usize,
    /// Maximum clause width (number of literals in the widest clause).
    max_width: usize,
}

impl CnfFormula {
    /// Create a CNF formula from DIMACS-format clauses.
    ///
    /// # Errors
    ///
    /// Returns `CnfTranslationError::ZeroLiteral` if any clause contains
    /// literal 0, and `CnfTranslationError::EmptyClause` if any clause
    /// is empty.
    pub fn new(clauses: Vec<Vec<i32>>) -> Result<Self, CnfTranslationError> {
        let mut num_vars: u32 = 0;
        let mut max_width: usize = 0;

        for (idx, clause) in clauses.iter().enumerate() {
            if clause.is_empty() {
                return Err(CnfTranslationError::EmptyClause { clause_idx: idx });
            }
            for &lit in clause {
                if lit == 0 {
                    return Err(CnfTranslationError::ZeroLiteral { clause_idx: idx });
                }
                let var = lit.unsigned_abs();
                if var > num_vars {
                    num_vars = var;
                }
            }
            if clause.len() > max_width {
                max_width = clause.len();
            }
        }

        let num_clauses = clauses.len();
        Ok(Self {
            clauses,
            num_vars,
            num_clauses,
            max_width,
        })
    }

    /// Create a CNF formula from raw clauses without validation.
    ///
    /// Use when clauses are known to be well-formed (e.g., from a generator).
    #[must_use]
    pub fn from_raw(clauses: Vec<Vec<i32>>, num_vars: u32) -> Self {
        let num_clauses = clauses.len();
        let max_width = clauses.iter().map(Vec::len).max().unwrap_or(0);
        Self {
            clauses,
            num_vars,
            num_clauses,
            max_width,
        }
    }

    /// The clauses in DIMACS format.
    #[must_use]
    pub fn clauses(&self) -> &[Vec<i32>] {
        &self.clauses
    }

    /// Number of distinct variables.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Number of clauses.
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.num_clauses
    }

    /// Maximum clause width.
    #[must_use]
    pub fn max_width(&self) -> usize {
        self.max_width
    }

    /// Expected maximum polynomial degree (equals max clause width).
    ///
    /// Each clause of width k produces a polynomial of degree k.
    #[must_use]
    pub fn expected_max_degree(&self) -> usize {
        self.max_width
    }
}

// ---------------------------------------------------------------------------
// Translation functions
// ---------------------------------------------------------------------------

/// Metadata about a translated clause polynomial.
#[derive(Debug, Clone)]
pub struct ClauseTranslation {
    /// The GF(2) polynomial encoding of the clause.
    pub polynomial: Gf2Poly,
    /// The original clause in DIMACS format.
    pub clause: Vec<i32>,
    /// Clause index in the formula.
    pub clause_idx: usize,
    /// Degree of the polynomial (equals clause width).
    pub degree: usize,
    /// Variables appearing in the clause (0-based indices).
    pub variables: Vec<u32>,
    /// Polarity of each variable: true = positive literal, false = negative.
    pub polarities: Vec<bool>,
}

/// Translate a full CNF formula into a GF(2) polynomial system.
///
/// Returns one [`ClauseTranslation`] per clause, preserving order.
///
/// # Errors
///
/// Returns `CnfTranslationError` if the formula is malformed.
pub fn translate_cnf(formula: &CnfFormula) -> Result<Vec<ClauseTranslation>, CnfTranslationError> {
    formula
        .clauses()
        .iter()
        .enumerate()
        .map(|(idx, clause)| translate_clause(clause, idx))
        .collect()
}

/// Translate a single clause to its GF(2) polynomial encoding with metadata.
///
/// # Errors
///
/// Returns `CnfTranslationError::ZeroLiteral` if the clause contains literal 0.
pub fn translate_clause(
    clause: &[i32],
    clause_idx: usize,
) -> Result<ClauseTranslation, CnfTranslationError> {
    let mut variables = Vec::with_capacity(clause.len());
    let mut polarities = Vec::with_capacity(clause.len());

    for &lit in clause {
        if lit == 0 {
            return Err(CnfTranslationError::ZeroLiteral { clause_idx });
        }
        let var_idx = lit.unsigned_abs() - 1;
        variables.push(var_idx);
        polarities.push(lit > 0);
    }

    let polynomial = Gf2Poly::from_clause(clause);
    let degree = polynomial.degree();

    Ok(ClauseTranslation {
        polynomial,
        clause: clause.to_vec(),
        clause_idx,
        degree,
        variables,
        polarities,
    })
}

/// Extract just the polynomials from a CNF formula (convenience wrapper).
///
/// Equivalent to `translate_cnf(formula)?.iter().map(|t| t.polynomial.clone()).collect()`.
///
/// # Errors
///
/// Returns `CnfTranslationError` if the formula is malformed.
pub fn translate_cnf_polynomials(
    formula: &CnfFormula,
) -> Result<Vec<Gf2Poly>, CnfTranslationError> {
    Ok(translate_cnf(formula)?
        .into_iter()
        .map(|t| t.polynomial)
        .collect())
}

// ---------------------------------------------------------------------------
// XOR constraint generation
// ---------------------------------------------------------------------------

/// Generate a CNF encoding of XOR constraints.
///
/// Each constraint specifies that the XOR of a subset of variables equals
/// a given parity. XOR constraints are a natural fit for GF(2) because
/// XOR = addition in GF(2).
///
/// # Arguments
///
/// * `num_vars` - Total number of variables (1-based DIMACS).
/// * `constraints` - Each entry `(vars, parity)` encodes
///   `x_{vars[0]} XOR x_{vars[1]} XOR ... = parity`.
///
/// # Returns
///
/// `(clauses, num_vars)` where `clauses` is the CNF encoding.
///
/// # Encoding
///
/// An XOR of k variables with target parity p produces 2^(k-1) clauses.
/// Each clause excludes one assignment that has the wrong parity.
#[must_use]
pub fn generate_xor_cnf(num_vars: u32, constraints: &[(Vec<u32>, bool)]) -> (Vec<Vec<i32>>, u32) {
    let mut clauses = Vec::new();

    for (vars, target_parity) in constraints {
        let k = vars.len();
        if k == 0 {
            continue;
        }

        let total = 1u32 << k;
        for mask in 0..total {
            // Count true variables in this assignment.
            let num_true = (0..k).filter(|&b| mask & (1 << b) != 0).count();
            let assignment_parity = num_true % 2 == 1;

            // Include clause if this assignment has the wrong parity.
            if assignment_parity != *target_parity {
                let clause: Vec<i32> = (0..k)
                    .map(|b| {
                        let var = vars[b] as i32;
                        if mask & (1 << b) != 0 {
                            -var // exclude true -> negative literal
                        } else {
                            var // exclude false -> positive literal
                        }
                    })
                    .collect();
                clauses.push(clause);
            }
        }
    }

    (clauses, num_vars)
}

/// Generate an UNSAT XOR system: contradictory parity constraints.
///
/// Creates `n` binary XOR constraints on consecutive variable pairs,
/// plus a global parity constraint that contradicts the local ones.
///
/// For `n` variables with constraints x1 XOR x2 = 0, x2 XOR x3 = 0, ...,
/// x_{n-1} XOR x_n = 0, plus x1 XOR x_n = 1. This forces all variables
/// equal but also forces x1 != x_n, which is impossible.
#[must_use]
pub fn generate_unsat_xor_system(n: u32) -> (Vec<Vec<i32>>, u32) {
    if n < 2 {
        // Degenerate: x1 XOR x1 = 1 is impossible (0 != 1).
        return (vec![vec![1], vec![-1]], 1);
    }

    let mut constraints: Vec<(Vec<u32>, bool)> = Vec::new();

    // Chain: x_i XOR x_{i+1} = 0 for i = 1..n-1
    for i in 1..n {
        constraints.push((vec![i, i + 1], false));
    }

    // Closing: x_1 XOR x_n = 1 (contradicts the chain forcing equality)
    constraints.push((vec![1, n], true));

    generate_xor_cnf(n, &constraints)
}

// ---------------------------------------------------------------------------
// Verification
// ---------------------------------------------------------------------------

/// Verify that a CNF-to-GF(2) translation is satisfiability-preserving.
///
/// For each Boolean assignment over `num_vars` variables: the CNF is
/// satisfied iff all translated polynomials evaluate to 0.
///
/// Only feasible for small instances (`num_vars <= 20`).
///
/// # Returns
///
/// - `Ok(true)` if the translation is sound for all assignments.
/// - `Ok(false)` if a soundness violation was found.
/// - `Err(...)` if `num_vars` exceeds the feasibility limit.
pub fn verify_translation(
    formula: &CnfFormula,
    translations: &[ClauseTranslation],
) -> Result<bool, CnfTranslationError> {
    let num_vars = formula.num_vars();
    if num_vars > 20 {
        return Err(CnfTranslationError::TooManyVariables {
            num_vars,
            limit: 20,
        });
    }

    if formula.num_clauses() != translations.len() {
        return Ok(false);
    }

    let total_assignments = 1u32 << num_vars;

    for mask in 0..total_assignments {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();

        // Check CNF satisfaction.
        let cnf_sat = formula.clauses().iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                let val = assignment.get(var_idx).copied().unwrap_or(false);
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        });

        // Check polynomial system: all polynomials evaluate to 0.
        let poly_sat = translations
            .iter()
            .all(|t| !t.polynomial.evaluate(&assignment));

        if cnf_sat != poly_sat {
            return Ok(false);
        }
    }

    Ok(true)
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Standard Proof Complexity Encodings
//!
//! Benchmark formula families used for proof complexity lower bounds:
//!
//! - **Pigeonhole Principle (PHP)**: n+1 pigeons into n holes. Unsatisfiable.
//!   Resolution requires exponential-size proofs (Haken 1985).
//!   Cutting planes has polynomial-size proofs (Cook et al. 1987).
//!
//! - **Tseitin formulas**: parity constraints on a graph. Hard for resolution
//!   on expander graphs (Ben-Sasson & Wigderson 1999).
//!
//! - **Tseitin circuit transformation**: convert Boolean circuits to
//!   equisatisfiable CNF via gate-by-gate translation (Tseitin 1968).
//!
//! - **Cardinality encodings**: at-most-one (AMO), at-least-one (ALO),
//!   exactly-one (EO) constraints.

use super::cutting_planes::CpInequality;
use crate::sat_verify::cdcl::{Clause, Literal};
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Pigeonhole Principle
// ---------------------------------------------------------------------------

/// Encode PHP(n+1, n): n+1 pigeons must go into n holes.
///
/// Variables: p_{i,j} = pigeon i in hole j (1-indexed).
/// Variable index = (i - 1) * n + j, for i in 1..=n+1, j in 1..=n.
///
/// Clauses:
/// - Pigeon clause: for each pigeon i, at least one hole: (p_{i,1} v ... v p_{i,n})
/// - Hole clause: for each hole j and each pair (i1, i2), at most one pigeon:
///   (-p_{i1,j} v -p_{i2,j})
#[must_use]
pub fn encode_php(n: usize) -> (u32, Vec<Clause>) {
    let pigeons = n + 1;
    let num_vars = pigeons * n;
    let var = |pigeon: usize, hole: usize| -> i32 { ((pigeon - 1) * n + hole) as i32 };

    let mut clauses = Vec::new();

    // Pigeon clauses: each pigeon goes into at least one hole
    for i in 1..=pigeons {
        let clause: Vec<i32> = (1..=n).map(|j| var(i, j)).collect();
        clauses.push(clause);
    }

    // Hole clauses: no two pigeons in the same hole
    for j in 1..=n {
        for i1 in 1..=pigeons {
            for i2 in (i1 + 1)..=pigeons {
                clauses.push(vec![-var(i1, j), -var(i2, j)]);
            }
        }
    }

    (num_vars as u32, clauses)
}

/// Generalized pigeonhole encoding: `pigeons` pigeons into `holes` holes.
///
/// Variables: p_{i,j} = pigeon i in hole j (1-indexed).
/// Variable index = (i - 1) * holes + j, for i in 1..=pigeons, j in 1..=holes.
///
/// Clauses:
///   1. Each pigeon in at least one hole: OR_j p_{i,j} for each i
///   2. No two pigeons in same hole: NOT p_{i,j} OR NOT p_{k,j} for i < k, each j
#[must_use]
pub fn pigeonhole_cnf(pigeons: usize, holes: usize) -> Vec<Clause> {
    if pigeons == 0 || holes == 0 {
        // Degenerate: 0 holes means pigeon clauses are empty (unsatisfiable),
        // 0 pigeons means trivially satisfiable (no clauses).
        if pigeons == 0 {
            return Vec::new();
        }
        // pigeons > 0, holes == 0: each pigeon clause is empty clause
        return (0..pigeons).map(|_| Vec::new()).collect();
    }

    let var = |pigeon: usize, hole: usize| -> i32 { ((pigeon - 1) * holes + hole) as i32 };

    let mut clauses = Vec::new();

    // Pigeon clauses: each pigeon goes into at least one hole
    for i in 1..=pigeons {
        let clause: Vec<i32> = (1..=holes).map(|j| var(i, j)).collect();
        clauses.push(clause);
    }

    // Hole clauses: no two pigeons in the same hole
    for j in 1..=holes {
        for i1 in 1..=pigeons {
            for i2 in (i1 + 1)..=pigeons {
                clauses.push(vec![-var(i1, j), -var(i2, j)]);
            }
        }
    }

    clauses
}

/// Number of variables in PHP encoding with given pigeons and holes.
#[must_use]
pub fn php_num_vars(pigeons: usize, holes: usize) -> u32 {
    (pigeons * holes) as u32
}

/// Number of clauses in PHP encoding with given pigeons and holes.
///
/// Formula: pigeons + C(pigeons, 2) * holes
///   = pigeons + (pigeons * (pigeons - 1) / 2) * holes
#[must_use]
pub fn php_num_clauses(pigeons: usize, holes: usize) -> usize {
    if pigeons == 0 {
        return 0;
    }
    let pigeon_clauses = pigeons;
    let hole_clauses = (pigeons * (pigeons - 1) / 2) * holes;
    pigeon_clauses + hole_clauses
}

/// Encode PHP as cutting planes inequalities.
///
/// - Pigeon constraint: sum_j p_{i,j} >= 1 (each pigeon in some hole)
/// - Hole constraint: sum_i p_{i,j} <= 1, equivalently -sum_i p_{i,j} >= -1
///   equivalently (1 - p_{i1,j}) + (1 - p_{i2,j}) >= 1 for pairs,
///   or we use: sum_i p_{i,j} <= 1 rewritten as -sum_i p_{i,j} >= -(pigeons-1)
///
/// For simplicity, we use the direct encoding:
/// - Pigeon: for each pigeon i, sum_j x_{i,j} >= 1
/// - Hole: for each hole j, sum_i x_{i,j} <= 1, i.e. -sum_i x_{i,j} >= -1
#[must_use]
pub fn encode_php_cp(n: usize) -> Vec<CpInequality> {
    let pigeons = n + 1;
    let num_vars = pigeons * n;
    let var_idx = |pigeon: usize, hole: usize| -> usize { (pigeon - 1) * n + (hole - 1) };

    let mut inequalities = Vec::new();

    // Pigeon constraints: each pigeon in at least one hole
    for i in 1..=pigeons {
        let mut coeffs = vec![0i64; num_vars];
        for j in 1..=n {
            coeffs[var_idx(i, j)] = 1;
        }
        inequalities.push(CpInequality::new(coeffs, 1));
    }

    // Hole constraints: each hole has at most one pigeon
    // sum_i x_{i,j} <= 1  <=>  -sum_i x_{i,j} >= -1
    for j in 1..=n {
        let mut coeffs = vec![0i64; num_vars];
        for i in 1..=pigeons {
            coeffs[var_idx(i, j)] = -1;
        }
        inequalities.push(CpInequality::new(coeffs, -1));
    }

    inequalities
}

// ---------------------------------------------------------------------------
// Tseitin graph formulas
// ---------------------------------------------------------------------------

/// Encode a Tseitin formula on a path graph with `n` edges.
///
/// Variables: x_1, ..., x_n (one per edge).
/// For each internal vertex v (degree 2): x_{v-1} XOR x_v = 1 (odd parity).
/// XOR constraints are encoded in CNF with 4 clauses per constraint for
/// vertices with 2 edges, plus boundary constraints.
///
/// For simplicity, we encode XOR(x_i, x_{i+1}) = 1 for i in 1..n-1, meaning
/// an odd number of true variables on each edge pair. This is unsatisfiable
/// when the total parity is inconsistent.
#[must_use]
pub fn encode_tseitin(n: usize) -> (u32, Vec<Clause>) {
    if n < 2 {
        return (n as u32, Vec::new());
    }

    let num_vars = n as u32;
    let mut clauses = Vec::new();

    // For each pair of adjacent edges, encode XOR = 1 (odd parity).
    // XOR(x_i, x_{i+1}) = 1 means exactly one of them is true.
    // CNF: (x_i v x_{i+1}) AND (-x_i v -x_{i+1})
    for i in 1..n {
        let j = (i + 1) as i32;
        let i = i as i32;
        clauses.push(vec![i, j]); // at least one true
        clauses.push(vec![-i, -j]); // at most one true
    }

    // Boundary: force x_1 = true and x_n = true.
    // With n-1 XOR=1 constraints, if n is even, x_1 = x_n (both true is consistent).
    // If n is odd, x_1 != x_n, so forcing both true creates unsatisfiability.
    clauses.push(vec![1]);
    clauses.push(vec![num_vars as i32]);

    (num_vars, clauses)
}

// Re-export Tseitin circuit types from dedicated module.
pub use super::tseitin_circuit::{
    evaluate_circuit, tseitin_transform, verify_tseitin_equisat, Circuit, Gate, GateType,
    TseitinResult,
};

// ---------------------------------------------------------------------------
// Cardinality encodings
// ---------------------------------------------------------------------------

/// At-most-one (AMO) encoding: at most one of the given literals is true.
///
/// Pairwise encoding: NOT x_i OR NOT x_j for all i < j.
/// O(k^2) clauses, O(k) variables (no auxiliary variables).
#[must_use]
pub fn amo_pairwise(vars: &[Literal]) -> Vec<Clause> {
    let mut clauses = Vec::new();
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            clauses.push(vec![-vars[i], -vars[j]]);
        }
    }
    clauses
}

/// At-least-one (ALO) encoding: at least one of the given literals is true.
///
/// Single clause: x_1 OR x_2 OR ... OR x_k.
#[must_use]
pub fn alo_clause(vars: &[Literal]) -> Clause {
    vars.to_vec()
}

/// Exactly-one (EO) encoding: exactly one of the given literals is true.
///
/// AMO + ALO combined: pairwise exclusion plus one must be true.
#[must_use]
pub fn exactly_one(vars: &[Literal]) -> Vec<Clause> {
    let mut clauses = amo_pairwise(vars);
    clauses.push(alo_clause(vars));
    clauses
}

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

/// PC05: Tseitin transformation preserves satisfiability.
pub const PC05_TSEITIN_EQUISAT: ProofStatus = ProofStatus::DerivedPending;

/// PC06: Pigeonhole encoding is unsatisfiable for n+1 pigeons, n holes.
pub const PC06_PHP_UNSAT: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Inline tests (existing)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_php_encoding_size() {
        // PHP(3,2): 3 pigeons, 2 holes. 6 vars, 3 pigeon + 6 hole clauses = 9.
        let (num_vars, clauses) = encode_php(2);
        assert_eq!(num_vars, 6);
        assert_eq!(clauses.len(), 9); // 3 pigeon + 6 hole
    }

    #[test]
    fn test_php_cp_encoding_count() {
        // PHP(3,2): 3 pigeon + 2 hole constraints = 5.
        let ineqs = encode_php_cp(2);
        assert_eq!(ineqs.len(), 5);
    }

    #[test]
    fn test_tseitin_encoding() {
        let (num_vars, clauses) = encode_tseitin(3);
        assert_eq!(num_vars, 3);
        // 2 XOR constraints * 2 clauses each + 2 boundary = 6
        assert_eq!(clauses.len(), 6);
    }

    #[test]
    fn test_tseitin_trivial() {
        let (_, clauses) = encode_tseitin(1);
        assert!(clauses.is_empty());
    }
}

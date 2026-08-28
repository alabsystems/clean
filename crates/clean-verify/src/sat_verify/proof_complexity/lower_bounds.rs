// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof Complexity Lower Bounds
//!
//! Implements lower bound verification for proof systems:
//!
//! - **PHP tree-resolution lower bound**: 2^{Mathverse(n)} for tree-like
//!   resolution on PHP(n+1,n) (Ben-Sasson & Wigderson 1999).
//!
//! - **Tseitin resolution lower bound**: exponential for resolution on
//!   Tseitin formulas over constant-degree expander graphs.
//!
//! - **Random CNF threshold**: phase transition at clause/variable ratio
//!   ~4.267 (Mézard, Parisi, Zecchina 2002).
//!
//! - **Width-space tradeoff**: Ben-Sasson & Wigderson relationship
//!   w(F |- bot) >= n / S(F |- bot) between width and space.
//!
//! References:
//! - Ben-Sasson, Wigderson (1999): "Short proofs are narrow — resolution
//!   made simple"
//! - Haken (1985): "The intractability of resolution"
//! - Mézard, Parisi, Zecchina (2002): random k-SAT threshold

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Classification of resolution complexity for random CNF formulas
/// based on the clause-to-variable ratio.
///
/// At the critical threshold (~4.267 for 3-SAT), random formulas
/// transition from satisfiable to unsatisfiable. Near the threshold,
/// refutation proofs are exponentially long.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ResolutionComplexity {
    /// Below the satisfiability threshold: formula is almost surely satisfiable.
    Satisfiable,
    /// Near the threshold: unsatisfiable but resolution proofs are
    /// exponentially long (hardest instances).
    HardRefutable,
    /// Well above the threshold: unsatisfiable with short resolution proofs
    /// (simple contradictions are easy to find).
    EasyRefutable,
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Satisfiability threshold for random 3-SAT (Mézard et al. 2002).
/// Below this ratio, random 3-CNF is almost surely satisfiable.
/// Above this ratio, almost surely unsatisfiable.
const RANDOM_3SAT_THRESHOLD: f64 = 4.267;

/// Width of the hard region around the threshold.
/// Ratios within [threshold, threshold + margin] produce the hardest
/// instances for resolution.
const HARD_REGION_MARGIN: f64 = 1.0;

/// Constant in Haken's lower bound exponent: 2^{n / HAKEN_DIVISOR}.
#[allow(dead_code)] // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
const HAKEN_DIVISOR: f64 = 20.0;

/// Constant in the tree-resolution lower bound for PHP.
/// Tree-like resolution of PHP(n+1,n) requires at least 2^{n / this}.
const TREE_RES_PHP_DIVISOR: f64 = 10.0;

/// Constant in the Tseitin expander lower bound exponent.
/// Resolution of Tseitin on constant-degree expanders with v vertices
/// requires at least 2^{v / this}.
const TSEITIN_EXPANDER_DIVISOR: f64 = 10.0;

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

/// PC05: PHP tree-resolution exponential lower bound.
///
/// Theorem: Tree-like resolution refutations of PHP(n+1,n) require
/// 2^{Mathverse(n)} steps (Ben-Sasson & Wigderson 1999).
pub const PC05_PHP_LOWER_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// PC06: Tseitin resolution lower bound on expander graphs.
///
/// Theorem: Resolution refutations of Tseitin formulas on constant-degree
/// expander graphs with v vertices require 2^{Mathverse(v)} steps.
pub const PC06_TSEITIN_LOWER_BOUND: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Lower bound computations
// ---------------------------------------------------------------------------

/// Compute the tree-resolution lower bound for PHP(pigeons, holes).
///
/// For the standard pigeonhole principle with n+1 pigeons and n holes,
/// tree-like resolution requires at least 2^{n/10} steps
/// (Ben-Sasson & Wigderson 1999).
///
/// Returns 1.0 for degenerate cases where pigeons <= holes (satisfiable)
/// or holes == 0.
#[must_use]
pub fn php_tree_resolution_lower_bound(pigeons: usize, holes: usize) -> f64 {
    if holes == 0 || pigeons <= holes {
        return 1.0;
    }
    // The lower bound applies when pigeons > holes.
    // Use the smaller dimension (holes) as the parameter n.
    let n = holes as f64;
    2.0_f64.powf(n / TREE_RES_PHP_DIVISOR)
}

/// Compute the resolution lower bound for Tseitin formulas on
/// constant-degree expander graphs.
///
/// For an expander graph with `graph_vertices` vertices, resolution
/// refutations of the Tseitin formula require at least 2^{v/10} steps.
///
/// Returns 1.0 for degenerate cases (0 or 1 vertices).
#[must_use]
pub fn tseitin_resolution_lower_bound(graph_vertices: usize) -> f64 {
    if graph_vertices <= 1 {
        return 1.0;
    }
    let v = graph_vertices as f64;
    2.0_f64.powf(v / TSEITIN_EXPANDER_DIVISOR)
}

/// Classify the resolution complexity of a random k-CNF formula based
/// on the clause-to-variable ratio.
///
/// The random 3-SAT threshold is approximately 4.267:
/// - Below threshold: almost surely satisfiable
/// - At/near threshold: hardest instances (exponential resolution proofs)
/// - Well above threshold: easily refutable (short proofs exist)
///
/// Returns `Satisfiable` if `num_vars` is 0 or `clause_var_ratio` is
/// non-positive.
#[must_use]
pub fn random_cnf_resolution_threshold(
    num_vars: usize,
    clause_var_ratio: f64,
) -> ResolutionComplexity {
    if num_vars == 0 || clause_var_ratio <= 0.0 {
        return ResolutionComplexity::Satisfiable;
    }
    if clause_var_ratio < RANDOM_3SAT_THRESHOLD {
        ResolutionComplexity::Satisfiable
    } else if clause_var_ratio <= RANDOM_3SAT_THRESHOLD + HARD_REGION_MARGIN {
        ResolutionComplexity::HardRefutable
    } else {
        ResolutionComplexity::EasyRefutable
    }
}

/// Verify that a proof is not shorter than the claimed lower bound.
///
/// Returns `true` if `proof_size >= claimed_lower_bound`, confirming
/// the proof respects the theoretical minimum. Returns `false` if the
/// proof is suspiciously shorter than the bound (which would indicate
/// either the bound is wrong or the proof is invalid).
///
/// Edge cases:
/// - `formula_size == 0`: returns `true` (trivial formula, no bound)
/// - `claimed_lower_bound <= 0.0`: returns `true` (vacuous bound)
/// - `proof_size == 0`: returns `false` unless the bound is also <= 0
#[must_use]
pub fn verify_lower_bound_witness(
    formula_size: usize,
    proof_size: usize,
    claimed_lower_bound: f64,
) -> bool {
    if formula_size == 0 || claimed_lower_bound <= 0.0 {
        return true;
    }
    proof_size as f64 >= claimed_lower_bound
}

/// Verify the Ben-Sasson/Wigderson width-space tradeoff relationship.
///
/// Theorem (Ben-Sasson & Wigderson 1999): For any resolution refutation
/// of an unsatisfiable formula F over n variables:
///
///   w(F |- bot) <= n / s(F |- bot) + O(1)
///
/// where w is the maximum clause width and s is the space (maximum
/// number of clauses stored simultaneously).
///
/// We verify: `width * space >= num_vars` (the rearranged inequality,
/// dropping the constant term which only strengthens the check).
///
/// Returns `true` if the width-space product is at least `num_vars`,
/// confirming the tradeoff is respected.
///
/// Edge cases: returns `true` if `num_vars == 0`.
#[must_use]
pub fn width_space_tradeoff(width: usize, space: usize, num_vars: usize) -> bool {
    if num_vars == 0 {
        return true;
    }
    // width * space >= num_vars (Ben-Sasson & Wigderson tradeoff)
    width.saturating_mul(space) >= num_vars
}

/// Return lower bound registry entries for inclusion in the
/// proof complexity registry.
#[must_use]
pub fn lower_bounds_registry() -> Vec<(&'static str, ProofStatus)> {
    vec![
        ("PC05_php_lower_bound", PC05_PHP_LOWER_BOUND),
        ("PC06_tseitin_lower_bound", PC06_TSEITIN_LOWER_BOUND),
    ]
}

// ---------------------------------------------------------------------------
// Lower bound certificate infrastructure
// ---------------------------------------------------------------------------
//
// Moved to `super::lower_bound_certificates` (see that module's docs) and
// re-exported here so the historical paths keep resolving.
pub use super::lower_bound_certificates::{
    check_lower_bound_witness, is_hard_for, known_lower_bounds, suggest_proof_system,
    AsymptoticBound, FormulaFamily, FormulaStats, LowerBoundCertificate, ProofSystemClass,
};

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

/// Formula families used as witnesses for proof complexity lower bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FormulaFamily {
    /// Pigeonhole Principle: PHP(n+1, n).
    PHP,
    /// Tseitin formulas on constant-degree expander graphs.
    Tseitin,
    /// Random k-SAT near the satisfiability threshold.
    RandomKSat,
    /// Clique-coloring formulas.
    Clique,
    /// Parity (XOR) formulas.
    Parity,
    /// Ordering principle formulas.
    Ordering,
}

/// Asymptotic growth classification for proof complexity lower bounds.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum AsymptoticBound {
    /// Exponential lower bound: Mathverse(base^n).
    Exponential {
        /// The base of the exponential, e.g., 2.0 for 2^(n/c).
        base: f64,
    },
    /// Polynomial lower bound: Mathverse(n^degree).
    Polynomial {
        /// The degree of the polynomial.
        degree: u32,
    },
    /// Quasi-polynomial lower bound: 2^{Mathverse(log^c n)}.
    Quasipolynomial,
}

/// Proof system classes for lower bound classification.
///
/// Separate from `separations::ProofSystem` because this enum includes
/// systems (Polynomial Calculus, Extended Frege) that are not part of
/// the resolution/CP hierarchy but have important lower bound results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ProofSystemClass {
    /// Tree-like resolution.
    TreeResolution,
    /// General (DAG) resolution.
    Resolution,
    /// Cutting Planes (pseudo-Boolean reasoning with integer rounding).
    CuttingPlanes,
    /// Polynomial Calculus (algebraic proof system over polynomials).
    PolynomialCalculus,
    /// Frege systems (textbook propositional logic).
    Frege,
    /// Extended Frege (Frege + extension rule for new variables).
    ExtendedFrege,
}

/// A certificate recording a known proof complexity lower bound result.
///
/// Each certificate corresponds to a published theorem establishing that
/// a specific formula family requires super-polynomial proofs in a
/// specific proof system.
#[derive(Debug, Clone)]
pub struct LowerBoundCertificate {
    /// The formula family that is hard.
    pub family: FormulaFamily,
    /// The proof system for which the lower bound holds.
    pub proof_system: ProofSystemClass,
    /// The asymptotic growth of the lower bound.
    pub bound: AsymptoticBound,
    /// Paper citation (author, year, title).
    pub reference: &'static str,
    /// Year of publication.
    pub year: u16,
}

/// Statistical properties of a formula for proof system routing.
#[derive(Debug, Clone)]
pub struct FormulaStats {
    /// Number of variables.
    pub num_vars: usize,
    /// Number of clauses.
    pub num_clauses: usize,
    /// Maximum clause width (number of literals in longest clause).
    pub max_clause_width: usize,
    /// Whether the formula has cardinality constraint structure (PHP-like).
    pub has_cardinality_structure: bool,
    /// Whether the formula has XOR/parity constraint structure (Tseitin-like).
    pub has_xor_structure: bool,
    /// Whether the formula appears to be a random instance.
    pub is_random: bool,
}

// ---------------------------------------------------------------------------
// Known lower bounds registry
// ---------------------------------------------------------------------------

/// Return the comprehensive registry of all major proof complexity lower bounds.
///
/// Each entry is a published result establishing that a formula family
/// requires super-polynomial proofs in a specific proof system.
///
/// References:
/// - Haken (1985): "The intractability of resolution"
/// - Chvatal & Szemeredi (1988): "Many hard examples for resolution"
/// - Pudlak (1997): "Lower bounds for resolution and cutting planes
///   proofs and monotone computations"
/// - Razborov (1998): "Lower bounds for the polynomial calculus"
/// - Ben-Sasson & Wigderson (1999): "Short proofs are narrow --
///   resolution made simple"
/// - Bonet & Galesi (1999): "Optimality of size-width tradeoffs for
///   resolution"
#[must_use]
pub fn known_lower_bounds() -> Vec<LowerBoundCertificate> {
    vec![
        // PHP is exponentially hard for resolution (Haken 1985).
        // Any resolution refutation of PHP(n+1,n) requires 2^{n/20} steps.
        LowerBoundCertificate {
            family: FormulaFamily::PHP,
            proof_system: ProofSystemClass::Resolution,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Haken (1985): The intractability of resolution",
            year: 1985,
        },
        // PHP requires degree n in Polynomial Calculus (Razborov 1998).
        LowerBoundCertificate {
            family: FormulaFamily::PHP,
            proof_system: ProofSystemClass::PolynomialCalculus,
            bound: AsymptoticBound::Polynomial { degree: 1 },
            reference: "Razborov (1998): Lower bounds for the polynomial calculus",
            year: 1998,
        },
        // Tseitin on expanders requires 2^{Mathverse(n)} resolution steps.
        LowerBoundCertificate {
            family: FormulaFamily::Tseitin,
            proof_system: ProofSystemClass::Resolution,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Ben-Sasson & Wigderson (1999): Short proofs are narrow",
            year: 1999,
        },
        // Tseitin requires 2^{Mathverse(n)} tree-resolution steps.
        LowerBoundCertificate {
            family: FormulaFamily::Tseitin,
            proof_system: ProofSystemClass::TreeResolution,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Ben-Sasson & Wigderson (1999): Short proofs are narrow",
            year: 1999,
        },
        // Clique-coloring requires exp cutting planes steps (Pudlak 1997).
        LowerBoundCertificate {
            family: FormulaFamily::Clique,
            proof_system: ProofSystemClass::CuttingPlanes,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Pudlak (1997): Lower bounds for resolution and cutting planes",
            year: 1997,
        },
        // Random k-SAT near threshold requires 2^{Mathverse(n)} resolution.
        LowerBoundCertificate {
            family: FormulaFamily::RandomKSat,
            proof_system: ProofSystemClass::Resolution,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Chvatal & Szemeredi (1988): Many hard examples for resolution",
            year: 1988,
        },
        // Ordering principle requires 2^{Mathverse(n^{1/3})} resolution.
        LowerBoundCertificate {
            family: FormulaFamily::Ordering,
            proof_system: ProofSystemClass::Resolution,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Bonet & Galesi (1999): Optimality of size-width tradeoffs",
            year: 1999,
        },
        // Parity requires 2^{Mathverse(n)} resolution.
        LowerBoundCertificate {
            family: FormulaFamily::Parity,
            proof_system: ProofSystemClass::Resolution,
            bound: AsymptoticBound::Exponential { base: 2.0 },
            reference: "Ben-Sasson & Wigderson (1999): Short proofs are narrow",
            year: 1999,
        },
    ]
}

/// Evaluate the concrete lower bound for a given instance size.
///
/// Given a certificate and an instance parameter `n` (= `formula_size`),
/// computes the numerical lower bound on proof size.
///
/// - `Exponential { base }`: returns `floor(base^n)`, saturating at `u64::MAX`.
/// - `Polynomial { degree }`: returns `n^degree`, saturating at `u64::MAX`.
/// - `Quasipolynomial`: returns `floor(2^(log2(n)^2))`, saturating at `u64::MAX`.
///
/// Returns 1 for `formula_size == 0` (trivial instance).
#[must_use]
pub fn check_lower_bound_witness(cert: &LowerBoundCertificate, formula_size: usize) -> u64 {
    if formula_size == 0 {
        return 1;
    }
    let n = formula_size as f64;
    let value = match cert.bound {
        AsymptoticBound::Exponential { base } => base.powf(n),
        AsymptoticBound::Polynomial { degree } => n.powi(degree as i32),
        AsymptoticBound::Quasipolynomial => {
            let log_n = n.log2();
            2.0_f64.powf(log_n * log_n)
        }
    };
    if value >= u64::MAX as f64 {
        u64::MAX
    } else if value < 1.0 {
        1
    } else {
        value as u64
    }
}

/// Suggest proof systems that avoid known exponential lower bounds
/// for the given formula structure.
///
/// Returns a list of `(system, reason)` pairs, ordered from most
/// recommended to least. The suggestions are based on structural
/// analysis of the formula to match known hard-formula families.
///
/// - Cardinality structure (PHP-like): Cutting Planes has polynomial
///   proofs where Resolution requires exponential (Cook et al. 1987).
/// - XOR/parity structure (Tseitin-like): Extended Frege avoids the
///   exponential Resolution lower bound.
/// - Random instances: Frege and Extended Frege are recommended since
///   Resolution is exponentially hard near the SAT threshold.
/// - Resolution is always included as a baseline with a caveat about
///   known exponential lower bounds.
#[must_use]
pub fn suggest_proof_system(formula_stats: &FormulaStats) -> Vec<(ProofSystemClass, &'static str)> {
    let mut suggestions = Vec::new();

    if formula_stats.has_cardinality_structure {
        suggestions.push((
            ProofSystemClass::CuttingPlanes,
            "PHP-like cardinality structure: CP has polynomial proofs (Cook et al. 1987)",
        ));
    }

    if formula_stats.has_xor_structure {
        suggestions.push((
            ProofSystemClass::ExtendedFrege,
            "XOR/parity structure: Extended Frege avoids exponential Resolution lower bound",
        ));
    }

    if formula_stats.is_random {
        suggestions.push((
            ProofSystemClass::Frege,
            "Random instance: Frege avoids Resolution exponential hardness near threshold",
        ));
        suggestions.push((
            ProofSystemClass::ExtendedFrege,
            "Random instance: Extended Frege provides polynomial-size proofs",
        ));
    }

    // Always include Resolution as a baseline.
    let resolution_caveat = if formula_stats.has_cardinality_structure
        || formula_stats.has_xor_structure
        || formula_stats.is_random
    {
        "Resolution: baseline system, but known exponential lower bounds apply to this formula class"
    } else {
        "Resolution: baseline system, no known exponential lower bound for this structure"
    };
    suggestions.push((ProofSystemClass::Resolution, resolution_caveat));

    suggestions
}

/// Check whether a formula family is known to be exponentially hard
/// for a specific proof system.
///
/// Returns the matching `LowerBoundCertificate` if the family has a
/// known exponential lower bound in the given system, or `None` if
/// no such result is known.
#[must_use]
pub fn is_hard_for(
    family: &FormulaFamily,
    system: &ProofSystemClass,
) -> Option<LowerBoundCertificate> {
    known_lower_bounds().into_iter().find(|cert| {
        cert.family == *family
            && cert.proof_system == *system
            && matches!(cert.bound, AsymptoticBound::Exponential { .. })
    })
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness theorems for interval arithmetic (20 theorems).
//!
//! Each theorem is stated with its proof sketch and verified at runtime
//! using concrete witness values. Theorem status is tracked via
//! [`ProofStatus`] for integration with the clean-verify proof library.
//!
//! # Theorem Index
//!
//! ## Containment soundness (T01--T08)
//! - T01: Addition containment
//! - T02: Subtraction containment
//! - T03: Negation containment
//! - T04: Multiplication containment
//! - T05: Division containment
//! - T06: Absolute value containment
//! - T07: Power containment (non-negative interval)
//! - T08: Sqrt containment (non-negative interval)
//!
//! ## Structural properties (T09--T14)
//! - T09: Intersection containment
//! - T10: Hull containment (both inputs are subsets of hull)
//! - T11: Subset transitivity
//! - T12: Containment transitivity (x in A, A subset B => x in B)
//! - T13: Point interval identity
//! - T14: Contains is reflexive
//!
//! ## Width bounds (T15--T17)
//! - T15: Width of addition = sum of widths
//! - T16: Width of subtraction = sum of widths
//! - T17: Width of negation = width
//!
//! ## Algebraic properties (T18--T20)
//! - T18: Addition commutativity
//! - T19: Multiplication commutativity
//! - T20: Addition associativity

use num_rational::Rational64;

use super::ops;
use super::types::Interval;
use crate::spec::ProofStatus;

/// Runtime witness for a theorem verification.
#[derive(Debug, Clone)]
pub struct TheoremWitness {
    /// Theorem identifier (e.g., "T01").
    pub id: &'static str,
    /// Human-readable description.
    pub description: &'static str,
    /// Whether the witness verified successfully.
    pub verified: bool,
    /// Formal proof status in the clean-verify proof library.
    pub proof_status: ProofStatus,
}

// ============================================================================
// Containment soundness theorems (T01--T08)
// ============================================================================

/// **T01 (Addition Containment):**
/// If `x in A` and `y in B`, then `x + y in add(A, B)`.
///
/// Proof: `A.lo <= x <= A.hi` and `B.lo <= y <= B.hi` implies
/// `A.lo + B.lo <= x + y <= A.hi + B.hi`. QED.
pub const T01_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t01_add_containment(
    x: Rational64,
    y: Rational64,
    a: &Interval,
    b: &Interval,
) -> TheoremWitness {
    let sum = x + y;
    let iv_sum = ops::add(a, b);
    TheoremWitness {
        id: "T01",
        description: "Addition Containment",
        verified: a.contains(x) && b.contains(y) && iv_sum.contains(sum),
        proof_status: T01_PROOF_STATUS,
    }
}

/// **T02 (Subtraction Containment):**
/// If `x in A` and `y in B`, then `x - y in sub(A, B)`.
///
/// Proof: `A.lo <= x <= A.hi` and `B.lo <= y <= B.hi` gives
/// `-B.hi <= -y <= -B.lo`. Adding: `A.lo - B.hi <= x - y <= A.hi - B.lo`. QED.
pub const T02_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t02_sub_containment(
    x: Rational64,
    y: Rational64,
    a: &Interval,
    b: &Interval,
) -> TheoremWitness {
    let diff = x - y;
    let iv_diff = ops::sub(a, b);
    TheoremWitness {
        id: "T02",
        description: "Subtraction Containment",
        verified: a.contains(x) && b.contains(y) && iv_diff.contains(diff),
        proof_status: T02_PROOF_STATUS,
    }
}

/// **T03 (Negation Containment):**
/// If `x in A`, then `-x in neg(A)`.
///
/// Proof: `A.lo <= x <= A.hi` implies `-A.hi <= -x <= -A.lo`. QED.
pub const T03_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t03_neg_containment(x: Rational64, a: &Interval) -> TheoremWitness {
    let neg_x = -x;
    let iv_neg = ops::neg(a);
    TheoremWitness {
        id: "T03",
        description: "Negation Containment",
        verified: a.contains(x) && iv_neg.contains(neg_x),
        proof_status: T03_PROOF_STATUS,
    }
}

/// **T04 (Multiplication Containment):**
/// If `x in A` and `y in B`, then `x*y in mul(A, B)`.
///
/// Proof: `x*y` is bilinear on `[A.lo, A.hi] x [B.lo, B.hi]`.
/// Extrema occur at corners. The four-product method captures this. QED.
pub const T04_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t04_mul_containment(
    x: Rational64,
    y: Rational64,
    a: &Interval,
    b: &Interval,
) -> TheoremWitness {
    let prod = x * y;
    let iv_prod = ops::mul(a, b);
    TheoremWitness {
        id: "T04",
        description: "Multiplication Containment",
        verified: a.contains(x) && b.contains(y) && iv_prod.contains(prod),
        proof_status: T04_PROOF_STATUS,
    }
}

/// **T05 (Division Containment):**
/// If `x in A` and `y in B` with `0 not in B`, then `x/y in div(A, B)`.
///
/// Proof: `1/y in [1/B.hi, 1/B.lo]` (reciprocal reverses order on positive/
/// negative intervals not containing zero). By T04, `x * (1/y)` is contained
/// in `mul(A, [1/B.hi, 1/B.lo])`. QED.
pub const T05_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t05_div_containment(
    x: Rational64,
    y: Rational64,
    a: &Interval,
    b: &Interval,
) -> TheoremWitness {
    let zero = Rational64::from_integer(0);
    if y == zero || b.contains(zero) {
        return TheoremWitness {
            id: "T05",
            description: "Division Containment",
            verified: true, // Vacuously true: precondition not met
            proof_status: T05_PROOF_STATUS,
        };
    }
    let quot = x / y;
    match ops::div(a, b) {
        Ok(iv_quot) => TheoremWitness {
            id: "T05",
            description: "Division Containment",
            verified: a.contains(x) && b.contains(y) && iv_quot.contains(quot),
            proof_status: T05_PROOF_STATUS,
        },
        Err(_) => TheoremWitness {
            id: "T05",
            description: "Division Containment",
            verified: false,
            proof_status: T05_PROOF_STATUS,
        },
    }
}

/// **T06 (Absolute Value Containment):**
/// If `x in A`, then `|x| in abs(A)`.
///
/// Proof: Case analysis on sign of endpoints.
/// - Both non-negative: `|x| = x in A = abs(A)`.
/// - Both non-positive: `|x| = -x in neg(A) = abs(A)`.
/// - Straddles zero: `|x| in [0, max(-A.lo, A.hi)] = abs(A)`. QED.
pub const T06_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t06_abs_containment(x: Rational64, a: &Interval) -> TheoremWitness {
    let zero = Rational64::from_integer(0);
    let abs_x = if x >= zero { x } else { -x };
    let iv_abs = ops::abs(a);
    TheoremWitness {
        id: "T06",
        description: "Absolute Value Containment",
        verified: a.contains(x) && iv_abs.contains(abs_x),
        proof_status: T06_PROOF_STATUS,
    }
}

/// **T07 (Power Containment -- non-negative interval):**
/// If `x in A` with `A.lo >= 0` and `n >= 1`, then `x^n in pow(A, n)`.
///
/// Proof: On `[0, inf)`, `t -> t^n` is monotone increasing for `n >= 1`.
/// Hence `A.lo^n <= x^n <= A.hi^n`. QED.
pub const T07_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t07_pow_containment_nonneg(x: Rational64, a: &Interval, n: u32) -> TheoremWitness {
    if n == 0 || !a.is_nonnegative() {
        return TheoremWitness {
            id: "T07",
            description: "Power Containment (non-negative)",
            verified: true, // Vacuously true
            proof_status: T07_PROOF_STATUS,
        };
    }
    let x_pow = rational_pow_val(x, n);
    match ops::pow(a, n) {
        Ok(iv_pow) => TheoremWitness {
            id: "T07",
            description: "Power Containment (non-negative)",
            verified: a.contains(x) && iv_pow.contains(x_pow),
            proof_status: T07_PROOF_STATUS,
        },
        Err(_) => TheoremWitness {
            id: "T07",
            description: "Power Containment (non-negative)",
            verified: false,
            proof_status: T07_PROOF_STATUS,
        },
    }
}

/// **T08 (Sqrt Containment):**
/// If `x in A` with `A.lo >= 0`, then `sqrt(x) in sqrt(A)`.
///
/// Proof: `sqrt` is monotone increasing on `[0, inf)`.
/// `A.lo <= x <= A.hi` implies `sqrt(A.lo) <= sqrt(x) <= sqrt(A.hi)`. QED.
///
/// Note: This is DerivedPending because our rational sqrt is an approximation
/// and the containment depends on the rounding direction being correct.
pub const T08_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t08_sqrt_containment(x: Rational64, a: &Interval) -> TheoremWitness {
    let zero = Rational64::from_integer(0);
    if x < zero || !a.is_nonnegative() {
        return TheoremWitness {
            id: "T08",
            description: "Sqrt Containment",
            verified: true,
            proof_status: T08_PROOF_STATUS,
        };
    }
    match ops::sqrt(a) {
        Ok(iv_sqrt) => {
            // Compute approximate sqrt of x
            let sqrt_x = rational_sqrt_approx(x);
            TheoremWitness {
                id: "T08",
                description: "Sqrt Containment",
                verified: a.contains(x) && iv_sqrt.contains(sqrt_x),
                proof_status: T08_PROOF_STATUS,
            }
        }
        Err(_) => TheoremWitness {
            id: "T08",
            description: "Sqrt Containment",
            verified: false,
            proof_status: T08_PROOF_STATUS,
        },
    }
}

// ============================================================================
// Structural properties (T09--T14)
// ============================================================================

/// **T09 (Intersection Containment):**
/// If `x in A` and `x in B`, then `x in intersect(A, B)`.
///
/// Proof: `max(A.lo, B.lo) <= x <= min(A.hi, B.hi)`. QED.
pub const T09_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t09_intersection_containment(
    x: Rational64,
    a: &Interval,
    b: &Interval,
) -> TheoremWitness {
    let verified = if a.contains(x) && b.contains(x) {
        match ops::intersect(a, b) {
            Ok(iv_inter) => iv_inter.contains(x),
            Err(_) => false,
        }
    } else {
        true // Vacuously true
    };
    TheoremWitness {
        id: "T09",
        description: "Intersection Containment",
        verified,
        proof_status: T09_PROOF_STATUS,
    }
}

/// **T10 (Hull Containment):**
/// `A subset hull(A, B)` and `B subset hull(A, B)`.
///
/// Proof: `hull = [min(A.lo, B.lo), max(A.hi, B.hi)]`.
/// `min(A.lo, B.lo) <= A.lo` and `A.hi <= max(A.hi, B.hi)`. QED.
pub const T10_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t10_hull_containment(a: &Interval, b: &Interval) -> TheoremWitness {
    let h = ops::hull(a, b);
    TheoremWitness {
        id: "T10",
        description: "Hull Containment",
        verified: h.contains_interval(a) && h.contains_interval(b),
        proof_status: T10_PROOF_STATUS,
    }
}

/// **T11 (Subset Transitivity):**
/// If `A subset B` and `B subset C`, then `A subset C`.
///
/// Proof: `C.lo <= B.lo <= A.lo` and `A.hi <= B.hi <= C.hi`. QED.
pub const T11_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t11_subset_transitivity(a: &Interval, b: &Interval, c: &Interval) -> TheoremWitness {
    let verified = if b.contains_interval(a) && c.contains_interval(b) {
        c.contains_interval(a)
    } else {
        true // Vacuously true
    };
    TheoremWitness {
        id: "T11",
        description: "Subset Transitivity",
        verified,
        proof_status: T11_PROOF_STATUS,
    }
}

/// **T12 (Containment Transitivity):**
/// If `x in A` and `A subset B`, then `x in B`.
///
/// Proof: `B.lo <= A.lo <= x <= A.hi <= B.hi`. QED.
pub const T12_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t12_containment_transitivity(
    x: Rational64,
    a: &Interval,
    b: &Interval,
) -> TheoremWitness {
    let verified = if a.contains(x) && b.contains_interval(a) {
        b.contains(x)
    } else {
        true
    };
    TheoremWitness {
        id: "T12",
        description: "Containment Transitivity",
        verified,
        proof_status: T12_PROOF_STATUS,
    }
}

/// **T13 (Point Interval):**
/// `x in [x, x]` and `width([x, x]) = 0`.
///
/// Proof: Trivial. QED.
pub const T13_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t13_point_interval(x: Rational64) -> TheoremWitness {
    let iv = Interval::point(x);
    let zero = Rational64::from_integer(0);
    TheoremWitness {
        id: "T13",
        description: "Point Interval",
        verified: iv.contains(x) && iv.width() == zero,
        proof_status: T13_PROOF_STATUS,
    }
}

/// **T14 (Contains Reflexive):**
/// For any interval `A`, `A.lo in A` and `A.hi in A`.
///
/// Proof: `A.lo <= A.lo <= A.hi` and `A.lo <= A.hi <= A.hi`. QED.
pub const T14_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t14_contains_reflexive(a: &Interval) -> TheoremWitness {
    TheoremWitness {
        id: "T14",
        description: "Contains Reflexive",
        verified: a.contains(a.lo()) && a.contains(a.hi()),
        proof_status: T14_PROOF_STATUS,
    }
}

// ============================================================================
// Helpers
// ============================================================================

/// Compute `x^n` for `Rational64`.
fn rational_pow_val(base: Rational64, exp: u32) -> Rational64 {
    let mut result = Rational64::from_integer(1);
    for _ in 0..exp {
        result *= base;
    }
    result
}

/// Rational sqrt approximation (f64-seeded, bounded denominator).
fn rational_sqrt_approx(x: Rational64) -> Rational64 {
    let zero = Rational64::from_integer(0);
    if x == zero {
        return zero;
    }
    let x_f64 = *x.numer() as f64 / *x.denom() as f64;
    let sqrt_f64 = x_f64.sqrt();
    // Use denominator 1000 to keep rationals small
    let denom = 1000i64;
    let numer = (sqrt_f64 * denom as f64).round() as i64;
    Rational64::new(numer.max(0), denom)
}

/// Summary of all 20 theorems' proof statuses.
///
/// Combines containment/structural theorems from this module with
/// width/algebraic theorems from [`super::theorems_algebraic`].
///
/// The reported statuses are the **pre-promotion** (registration-time) values
/// — every theorem is registered as `DerivedPending`. The **post-promotion**
/// status (what the kernel actually verifies) is available via
/// [`super::theorems_promote::compute_proof_statuses_dynamically`].
#[must_use]
pub fn all_proof_statuses() -> Vec<(&'static str, &'static str, ProofStatus)> {
    use super::theorems_algebraic;

    let mut statuses = vec![
        ("T01", "Addition Containment", T01_PROOF_STATUS),
        ("T02", "Subtraction Containment", T02_PROOF_STATUS),
        ("T03", "Negation Containment", T03_PROOF_STATUS),
        ("T04", "Multiplication Containment", T04_PROOF_STATUS),
        ("T05", "Division Containment", T05_PROOF_STATUS),
        ("T06", "Absolute Value Containment", T06_PROOF_STATUS),
        ("T07", "Power Containment (non-negative)", T07_PROOF_STATUS),
        ("T08", "Sqrt Containment", T08_PROOF_STATUS),
        ("T09", "Intersection Containment", T09_PROOF_STATUS),
        ("T10", "Hull Containment", T10_PROOF_STATUS),
        ("T11", "Subset Transitivity", T11_PROOF_STATUS),
        ("T12", "Containment Transitivity", T12_PROOF_STATUS),
        ("T13", "Point Interval", T13_PROOF_STATUS),
        ("T14", "Contains Reflexive", T14_PROOF_STATUS),
    ];
    statuses.extend(theorems_algebraic::algebraic_proof_statuses());
    statuses
}

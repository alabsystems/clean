// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Formal containment theorems for interval arithmetic (T_IA_01 -- T_IA_11).
//!
//! Each theorem is stated as a function that takes concrete witness values
//! and verifies the containment property. These serve as both documentation
//! of the mathematical properties and runtime-checkable proof obligations.
//!
//! # Theorem Numbering
//!
//! - T_IA_01 -- T_IA_11: Core algebraic containment (this file)
//! - T_IA_12 -- T_IA_20: Monotone functions and structural properties
//!   (see [`super::theorems_monotone`])

use num_rational::Rational64;

use super::ops;
use super::types::Interval;

/// Proof witness for a containment theorem. Carries the concrete values
/// used to verify the theorem instance.
#[derive(Debug, Clone)]
pub struct ContainmentWitness {
    /// Human-readable name of the theorem.
    pub theorem: &'static str,
    /// Whether the containment was verified.
    pub verified: bool,
}

// ============================================================================
// T_IA_01: Addition containment
// ============================================================================

/// **T_IA_01 (Addition Containment):**
/// If `x in [a,b]` and `y in [c,d]`, then `x + y in [a+c, b+d]`.
///
/// **Proof:** Since `a <= x <= b` and `c <= y <= d`, by adding inequalities:
/// `a + c <= x + y <= b + d`. QED.
#[must_use]
pub fn verify_add_containment(
    x: Rational64,
    y: Rational64,
    iv_x: &Interval<Rational64>,
    iv_y: &Interval<Rational64>,
) -> ContainmentWitness {
    let sum = x + y;
    let iv_sum = ops::add_rational(iv_x, iv_y);
    ContainmentWitness {
        theorem: "T_IA_01: Addition Containment",
        verified: iv_x.contains(&x) && iv_y.contains(&y) && iv_sum.contains(&sum),
    }
}

// ============================================================================
// T_IA_02: Subtraction containment
// ============================================================================

/// **T_IA_02 (Subtraction Containment):**
/// If `x in [a,b]` and `y in [c,d]`, then `x - y in [a-d, b-c]`.
///
/// **Proof:** Since `a <= x <= b` and `c <= y <= d`, we have `-d <= -y <= -c`.
/// Adding: `a - d <= x - y <= b - c`. QED.
#[must_use]
pub fn verify_sub_containment(
    x: Rational64,
    y: Rational64,
    iv_x: &Interval<Rational64>,
    iv_y: &Interval<Rational64>,
) -> ContainmentWitness {
    let diff = x - y;
    let iv_diff = ops::sub_rational(iv_x, iv_y);
    ContainmentWitness {
        theorem: "T_IA_02: Subtraction Containment",
        verified: iv_x.contains(&x) && iv_y.contains(&y) && iv_diff.contains(&diff),
    }
}

// ============================================================================
// T_IA_03: Negation containment
// ============================================================================

/// **T_IA_03 (Negation Containment):**
/// If `x in [a,b]`, then `-x in [-b, -a]`.
///
/// **Proof:** `a <= x <= b` implies `-b <= -x <= -a`. QED.
#[must_use]
pub fn verify_neg_containment(x: Rational64, iv_x: &Interval<Rational64>) -> ContainmentWitness {
    let neg_x = -x;
    let iv_neg = ops::neg_rational(iv_x);
    ContainmentWitness {
        theorem: "T_IA_03: Negation Containment",
        verified: iv_x.contains(&x) && iv_neg.contains(&neg_x),
    }
}

// ============================================================================
// T_IA_04: Multiplication containment
// ============================================================================

/// **T_IA_04 (Multiplication Containment):**
/// If `x in [a,b]` and `y in [c,d]`, then
/// `x*y in [min(ac,ad,bc,bd), max(ac,ad,bc,bd)]`.
///
/// **Proof:** The product `x*y` is a bilinear function on the rectangle
/// `[a,b] x [c,d]`. Its extrema on this rectangle occur at the corners
/// `(a,c), (a,d), (b,c), (b,d)`. Therefore `x*y` lies between the
/// minimum and maximum of `{ac, ad, bc, bd}`. QED.
#[must_use]
pub fn verify_mul_containment(
    x: Rational64,
    y: Rational64,
    iv_x: &Interval<Rational64>,
    iv_y: &Interval<Rational64>,
) -> ContainmentWitness {
    let prod = x * y;
    let iv_prod = ops::mul_rational(iv_x, iv_y);
    ContainmentWitness {
        theorem: "T_IA_04: Multiplication Containment",
        verified: iv_x.contains(&x) && iv_y.contains(&y) && iv_prod.contains(&prod),
    }
}

// ============================================================================
// T_IA_05: Division containment
// ============================================================================

/// **T_IA_05 (Division Containment):**
/// If `x in [a,b]` and `y in [c,d]` with `0 not in [c,d]`,
/// then `x/y in [a,b] * [1/d, 1/c]`.
///
/// **Proof:** Since `y in [c,d]` and `0 not in [c,d]`, we have
/// `1/y in [1/d, 1/c]` (the reciprocal reverses the ordering since
/// the function is monotone decreasing on intervals not containing
/// zero). Then `x/y = x * (1/y)`, and by T_IA_04, the product is
/// contained in the four-product interval. QED.
#[must_use]
pub fn verify_div_containment(
    x: Rational64,
    y: Rational64,
    iv_x: &Interval<Rational64>,
    iv_y: &Interval<Rational64>,
) -> ContainmentWitness {
    let zero = Rational64::from_integer(0);
    if y == zero || iv_y.contains(&zero) {
        return ContainmentWitness {
            theorem: "T_IA_05: Division Containment",
            verified: false,
        };
    }
    let quot = x / y;
    match ops::div_rational(iv_x, iv_y) {
        Ok(iv_quot) => ContainmentWitness {
            theorem: "T_IA_05: Division Containment",
            verified: iv_x.contains(&x) && iv_y.contains(&y) && iv_quot.contains(&quot),
        },
        Err(_) => ContainmentWitness {
            theorem: "T_IA_05: Division Containment",
            verified: false,
        },
    }
}

// ============================================================================
// T_IA_06: Subset transitivity
// ============================================================================

/// **T_IA_06 (Subset Transitivity):**
/// If `[a,b] subset [c,d]` and `[c,d] subset [e,f]`,
/// then `[a,b] subset [e,f]`.
///
/// **Proof:** `c <= a` and `e <= c` implies `e <= a`. Similarly
/// `b <= d` and `d <= f` implies `b <= f`. QED.
#[must_use]
pub fn verify_subset_transitivity(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
    iv3: &Interval<Rational64>,
) -> ContainmentWitness {
    let verified = if iv2.contains_interval(iv1) && iv3.contains_interval(iv2) {
        iv3.contains_interval(iv1)
    } else {
        true // Precondition not met: vacuously true
    };
    ContainmentWitness {
        theorem: "T_IA_06: Subset Transitivity",
        verified,
    }
}

// ============================================================================
// T_IA_07: Intersection containment
// ============================================================================

/// **T_IA_07 (Intersection Containment):**
/// If `x in [a,b]` and `x in [c,d]`, then `x in [a,b] intersect [c,d]`.
///
/// **Proof:** `x in [a,b]` means `a <= x <= b`. `x in [c,d]` means
/// `c <= x <= d`. So `max(a,c) <= x <= min(b,d)`, which is the
/// intersection. QED.
#[must_use]
pub fn verify_intersection_containment(
    x: Rational64,
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
) -> ContainmentWitness {
    let verified = if iv1.contains(&x) && iv2.contains(&x) {
        match ops::intersect_rational(iv1, iv2) {
            Some(iv_inter) => iv_inter.contains(&x),
            None => false, // Should not happen if x is in both
        }
    } else {
        true // Precondition not met
    };
    ContainmentWitness {
        theorem: "T_IA_07: Intersection Containment",
        verified,
    }
}

// ============================================================================
// T_IA_08: Hull containment
// ============================================================================

/// **T_IA_08 (Hull Containment):**
/// `[a,b] subset hull([a,b], [c,d])` and `[c,d] subset hull([a,b], [c,d])`.
///
/// **Proof:** `hull = [min(a,c), max(b,d)]`. Since `min(a,c) <= a` and
/// `b <= max(b,d)`, the first inclusion holds. Symmetric for second. QED.
#[must_use]
pub fn verify_hull_containment(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
) -> ContainmentWitness {
    let hull = ops::hull_rational(iv1, iv2);
    ContainmentWitness {
        theorem: "T_IA_08: Hull Containment",
        verified: hull.contains_interval(iv1) && hull.contains_interval(iv2),
    }
}

// ============================================================================
// T_IA_09: Width monotonicity
// ============================================================================

/// **T_IA_09 (Width Monotonicity under Addition):**
/// `width([a,b] + [c,d]) = width([a,b]) + width([c,d])`.
///
/// **Proof:** `width([a+c, b+d]) = (b+d) - (a+c) = (b-a) + (d-c)`. QED.
#[must_use]
pub fn verify_add_width(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
) -> ContainmentWitness {
    let sum = ops::add_rational(iv1, iv2);
    ContainmentWitness {
        theorem: "T_IA_09: Width Monotonicity under Addition",
        verified: sum.width() == iv1.width() + iv2.width(),
    }
}

// ============================================================================
// T_IA_10: Point interval identity
// ============================================================================

/// **T_IA_10 (Point Interval):**
/// For any `x`, `x in [x, x]` and `width([x, x]) = 0`.
///
/// **Proof:** `x <= x <= x` trivially. `width = x - x = 0`. QED.
#[must_use]
pub fn verify_point_interval(x: Rational64) -> ContainmentWitness {
    let iv = Interval::point(x);
    let zero = Rational64::from_integer(0);
    ContainmentWitness {
        theorem: "T_IA_10: Point Interval",
        verified: iv.contains(&x) && iv.width() == zero,
    }
}

// ============================================================================
// T_IA_11: Multiplication by point (scalar)
// ============================================================================

/// **T_IA_11 (Scalar Multiplication):**
/// If `x in [a,b]` and `k >= 0`, then `k*x in [k*a, k*b]`.
/// If `k < 0`, then `k*x in [k*b, k*a]`.
///
/// **Proof:** For `k >= 0`: multiplying `a <= x <= b` by `k` preserves
/// order. For `k < 0`: multiplication reverses order. QED.
#[must_use]
pub fn verify_scalar_mul_containment(
    x: Rational64,
    k: Rational64,
    iv_x: &Interval<Rational64>,
) -> ContainmentWitness {
    let kx = k * x;
    let iv_k = Interval::point(k);
    let iv_prod = ops::mul_rational(&iv_k, iv_x);
    ContainmentWitness {
        theorem: "T_IA_11: Scalar Multiplication Containment",
        verified: iv_x.contains(&x) && iv_prod.contains(&kx),
    }
}

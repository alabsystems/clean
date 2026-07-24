// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monotone function and structural theorems for interval arithmetic.
//!
//! Theorems T_IA_12 through T_IA_20: monotone function containment
//! (exp, ln, sqrt), width properties, and algebraic identities.

use num_rational::Rational64;

use super::ops;
use super::theorems::ContainmentWitness;
use super::types::Interval;

// ============================================================================
// T_IA_12: Monotone function containment
// ============================================================================

/// **T_IA_12 (Monotone Increasing Function):**
/// If `f` is monotone increasing and `x in [a,b]`, then `f(x) in [f(a), f(b)]`.
///
/// **Proof:** Monotone increasing means `a <= x <= b` implies `f(a) <= f(x) <= f(b)`. QED.
///
/// This is the foundation for exp, sqrt, and ln containment.
#[must_use]
pub fn verify_monotone_increasing(
    x: f64,
    iv_x: &Interval<f64>,
    f: fn(f64) -> f64,
) -> ContainmentWitness {
    if !iv_x.contains(&x) {
        return ContainmentWitness {
            theorem: "T_IA_12: Monotone Increasing Function",
            verified: true, // Vacuously true
        };
    }
    let fx = f(x);
    let iv_result = Interval::new(f(*iv_x.lower()), f(*iv_x.upper()));
    let verified = match iv_result {
        Ok(iv) => iv.contains(&fx),
        Err(_) => false,
    };
    ContainmentWitness {
        theorem: "T_IA_12: Monotone Increasing Function",
        verified,
    }
}

// ============================================================================
// T_IA_13: Exp containment (instance of T_IA_12)
// ============================================================================

/// **T_IA_13 (Exp Containment):**
/// If `x in [a,b]`, then `exp(x) in [exp(a), exp(b)]`.
///
/// **Proof:** `exp` is monotone increasing (derivative `exp(x) > 0` everywhere).
/// By T_IA_12, containment follows. QED.
#[must_use]
pub fn verify_exp_containment(x: f64, iv_x: &Interval<f64>) -> ContainmentWitness {
    if !iv_x.contains(&x) {
        return ContainmentWitness {
            theorem: "T_IA_13: Exp Containment",
            verified: true,
        };
    }
    let exp_x = x.exp();
    let iv_exp = ops::exp_f64(iv_x);
    ContainmentWitness {
        theorem: "T_IA_13: Exp Containment",
        verified: iv_exp.contains(&exp_x),
    }
}

// ============================================================================
// T_IA_14: Ln containment (instance of T_IA_12)
// ============================================================================

/// **T_IA_14 (Ln Containment):**
/// If `x in [a,b]` with `a > 0`, then `ln(x) in [ln(a), ln(b)]`.
///
/// **Proof:** `ln` is monotone increasing on `(0, inf)`. By T_IA_12. QED.
#[must_use]
pub fn verify_ln_containment(x: f64, iv_x: &Interval<f64>) -> ContainmentWitness {
    if !iv_x.contains(&x) || *iv_x.lower() <= 0.0 || x <= 0.0 {
        return ContainmentWitness {
            theorem: "T_IA_14: Ln Containment",
            verified: true,
        };
    }
    let ln_x = x.ln();
    match ops::ln_f64(iv_x) {
        Ok(iv_ln) => ContainmentWitness {
            theorem: "T_IA_14: Ln Containment",
            verified: iv_ln.contains(&ln_x),
        },
        Err(_) => ContainmentWitness {
            theorem: "T_IA_14: Ln Containment",
            verified: false,
        },
    }
}

// ============================================================================
// T_IA_15: Sqrt containment (instance of T_IA_12)
// ============================================================================

/// **T_IA_15 (Sqrt Containment):**
/// If `x in [a,b]` with `a >= 0`, then `sqrt(x) in [sqrt(a), sqrt(b)]`.
///
/// **Proof:** `sqrt` is monotone increasing on `[0, inf)`. By T_IA_12. QED.
#[must_use]
pub fn verify_sqrt_containment(x: f64, iv_x: &Interval<f64>) -> ContainmentWitness {
    if !iv_x.contains(&x) || *iv_x.lower() < 0.0 || x < 0.0 {
        return ContainmentWitness {
            theorem: "T_IA_15: Sqrt Containment",
            verified: true,
        };
    }
    let sqrt_x = x.sqrt();
    match ops::sqrt_f64(iv_x) {
        Ok(iv_sqrt) => ContainmentWitness {
            theorem: "T_IA_15: Sqrt Containment",
            verified: iv_sqrt.contains(&sqrt_x),
        },
        Err(_) => ContainmentWitness {
            theorem: "T_IA_15: Sqrt Containment",
            verified: false,
        },
    }
}

// ============================================================================
// T_IA_16: Subtraction width
// ============================================================================

/// **T_IA_16 (Width under Subtraction):**
/// `width([a,b] - [c,d]) = width([a,b]) + width([c,d])`.
///
/// **Proof:** `width([a-d, b-c]) = (b-c) - (a-d) = (b-a) + (d-c)`. QED.
#[must_use]
pub fn verify_sub_width(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
) -> ContainmentWitness {
    let diff = ops::sub_rational(iv1, iv2);
    ContainmentWitness {
        theorem: "T_IA_16: Width under Subtraction",
        verified: diff.width() == iv1.width() + iv2.width(),
    }
}

// ============================================================================
// T_IA_17: Double negation
// ============================================================================

/// **T_IA_17 (Double Negation):**
/// `-(-[a,b]) = [a,b]`.
///
/// **Proof:** `-[a,b] = [-b,-a]`. `-[-b,-a] = [a,b]`. QED.
#[must_use]
pub fn verify_double_negation(iv: &Interval<Rational64>) -> ContainmentWitness {
    let neg1 = ops::neg_rational(iv);
    let neg2 = ops::neg_rational(&neg1);
    ContainmentWitness {
        theorem: "T_IA_17: Double Negation",
        verified: neg2 == *iv,
    }
}

// ============================================================================
// T_IA_18: Multiplication commutativity
// ============================================================================

/// **T_IA_18 (Multiplication Commutativity):**
/// `[a,b] * [c,d] = [c,d] * [a,b]`.
///
/// **Proof:** The four products `{ac, ad, bc, bd}` are the same set regardless
/// of which factor is first. QED.
#[must_use]
pub fn verify_mul_commutativity(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
) -> ContainmentWitness {
    let prod1 = ops::mul_rational(iv1, iv2);
    let prod2 = ops::mul_rational(iv2, iv1);
    ContainmentWitness {
        theorem: "T_IA_18: Multiplication Commutativity",
        verified: prod1 == prod2,
    }
}

// ============================================================================
// T_IA_19: Addition commutativity
// ============================================================================

/// **T_IA_19 (Addition Commutativity):**
/// `[a,b] + [c,d] = [c,d] + [a,b]`.
///
/// **Proof:** `a+c = c+a` and `b+d = d+b`. QED.
#[must_use]
pub fn verify_add_commutativity(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
) -> ContainmentWitness {
    let sum1 = ops::add_rational(iv1, iv2);
    let sum2 = ops::add_rational(iv2, iv1);
    ContainmentWitness {
        theorem: "T_IA_19: Addition Commutativity",
        verified: sum1 == sum2,
    }
}

// ============================================================================
// T_IA_20: Addition associativity
// ============================================================================

/// **T_IA_20 (Addition Associativity):**
/// `([a,b] + [c,d]) + [e,f] = [a,b] + ([c,d] + [e,f])`.
///
/// **Proof:** Both sides equal `[a+c+e, b+d+f]` by associativity of
/// rational addition. QED.
#[must_use]
pub fn verify_add_associativity(
    iv1: &Interval<Rational64>,
    iv2: &Interval<Rational64>,
    iv3: &Interval<Rational64>,
) -> ContainmentWitness {
    let left = ops::add_rational(&ops::add_rational(iv1, iv2), iv3);
    let right = ops::add_rational(iv1, &ops::add_rational(iv2, iv3));
    ContainmentWitness {
        theorem: "T_IA_20: Addition Associativity",
        verified: left == right,
    }
}

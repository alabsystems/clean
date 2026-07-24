// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Width bounds and algebraic property theorems (T15--T20).
//!
//! Split from `theorems.rs` for the 500-line file limit.

use super::ops;
use super::theorems::TheoremWitness;
use super::types::Interval;
use crate::spec::ProofStatus;

// ============================================================================
// Width bounds (T15--T17)
// ============================================================================

/// **T15 (Width of Addition):**
/// `width(add(A, B)) = width(A) + width(B)`.
///
/// Proof: `width([A.lo+B.lo, A.hi+B.hi]) = (A.hi+B.hi) - (A.lo+B.lo)
///        = (A.hi-A.lo) + (B.hi-B.lo)`. QED.
pub const T15_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t15_add_width(a: &Interval, b: &Interval) -> TheoremWitness {
    let sum = ops::add(a, b);
    TheoremWitness {
        id: "T15",
        description: "Width of Addition",
        verified: sum.width() == a.width() + b.width(),
        proof_status: T15_PROOF_STATUS,
    }
}

/// **T16 (Width of Subtraction):**
/// `width(sub(A, B)) = width(A) + width(B)`.
///
/// Proof: `width([A.lo-B.hi, A.hi-B.lo]) = (A.hi-B.lo) - (A.lo-B.hi)
///        = (A.hi-A.lo) + (B.hi-B.lo)`. QED.
pub const T16_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t16_sub_width(a: &Interval, b: &Interval) -> TheoremWitness {
    let diff = ops::sub(a, b);
    TheoremWitness {
        id: "T16",
        description: "Width of Subtraction",
        verified: diff.width() == a.width() + b.width(),
        proof_status: T16_PROOF_STATUS,
    }
}

/// **T17 (Width of Negation):**
/// `width(neg(A)) = width(A)`.
///
/// Proof: `width([-A.hi, -A.lo]) = -A.lo - (-A.hi) = A.hi - A.lo`. QED.
pub const T17_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t17_neg_width(a: &Interval) -> TheoremWitness {
    let n = ops::neg(a);
    TheoremWitness {
        id: "T17",
        description: "Width of Negation",
        verified: n.width() == a.width(),
        proof_status: T17_PROOF_STATUS,
    }
}

// ============================================================================
// Algebraic properties (T18--T20)
// ============================================================================

/// **T18 (Addition Commutativity):**
/// `add(A, B) = add(B, A)`.
///
/// Proof: `A.lo + B.lo = B.lo + A.lo` and `A.hi + B.hi = B.hi + A.hi`. QED.
pub const T18_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t18_add_commutativity(a: &Interval, b: &Interval) -> TheoremWitness {
    let sum1 = ops::add(a, b);
    let sum2 = ops::add(b, a);
    TheoremWitness {
        id: "T18",
        description: "Addition Commutativity",
        verified: sum1 == sum2,
        proof_status: T18_PROOF_STATUS,
    }
}

/// **T19 (Multiplication Commutativity):**
/// `mul(A, B) = mul(B, A)`.
///
/// Proof: The set `{A.lo*B.lo, A.lo*B.hi, A.hi*B.lo, A.hi*B.hi}` is
/// invariant under swapping A and B. QED.
pub const T19_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t19_mul_commutativity(a: &Interval, b: &Interval) -> TheoremWitness {
    let prod1 = ops::mul(a, b);
    let prod2 = ops::mul(b, a);
    TheoremWitness {
        id: "T19",
        description: "Multiplication Commutativity",
        verified: prod1 == prod2,
        proof_status: T19_PROOF_STATUS,
    }
}

/// **T20 (Addition Associativity):**
/// `add(add(A, B), C) = add(A, add(B, C))`.
///
/// Proof: Both sides equal `[A.lo+B.lo+C.lo, A.hi+B.hi+C.hi]`
/// by associativity of rational addition. QED.
pub const T20_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[must_use]
pub fn verify_t20_add_associativity(a: &Interval, b: &Interval, c: &Interval) -> TheoremWitness {
    let left = ops::add(&ops::add(a, b), c);
    let right = ops::add(a, &ops::add(b, c));
    TheoremWitness {
        id: "T20",
        description: "Addition Associativity",
        verified: left == right,
        proof_status: T20_PROOF_STATUS,
    }
}

/// Proof statuses for theorems T15--T20.
#[must_use]
pub fn algebraic_proof_statuses() -> Vec<(&'static str, &'static str, ProofStatus)> {
    vec![
        ("T15", "Width of Addition", T15_PROOF_STATUS),
        ("T16", "Width of Subtraction", T16_PROOF_STATUS),
        ("T17", "Width of Negation", T17_PROOF_STATUS),
        ("T18", "Addition Commutativity", T18_PROOF_STATUS),
        ("T19", "Multiplication Commutativity", T19_PROOF_STATUS),
        ("T20", "Addition Associativity", T20_PROOF_STATUS),
    ]
}

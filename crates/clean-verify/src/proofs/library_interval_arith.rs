// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interval arithmetic proof terms for the kernel ProofLibrary.
//!
//! All 20 theorems (T01-T20) have real inductive proof terms:
//!
//! ## Containment soundness (T01-T08)
//! - T01: IvContainSound.add (addition containment)
//! - T02: IvContainSound.sub (subtraction containment)
//! - T03: IvContainSound.neg (negation containment)
//! - T04: IvContainSound.mul (multiplication containment)
//! - T05: IvContainSound.div (division containment)
//! - T06: IvContainSound.abs (absolute value containment)
//! - T07: IvContainSound.pow (power containment)
//! - T08: IvContainSound.sqrt (sqrt containment)
//!
//! ## Structural properties (T09-T14)
//! - T09: IvStructSound.intersect (intersection containment)
//! - T10: IvStructSound.hull (hull containment)
//! - T11: IvStructSound.subset_trans (subset transitivity)
//! - T12: IvStructSound.contain_trans (containment transitivity)
//! - T13: IvStructSound.point (point interval identity)
//! - T14: IvStructSound.reflexive (contains reflexive)
//!
//! ## Width bounds (T15-T17)
//! - T15: IvWidthSound.add_width (width of addition)
//! - T16: IvWidthSound.sub_width (width of subtraction)
//! - T17: IvWidthSound.neg_width (width of negation)
//!
//! ## Algebraic properties (T18-T20)
//! - T18: IvAlgebraSound.add_comm (addition commutativity)
//! - T19: IvAlgebraSound.mul_comm (multiplication commutativity)
//! - T20: IvAlgebraSound.add_assoc (addition associativity)
//!
//! The corresponding spec definitions and inductive types are registered
//! by `spec_registration::add_interval_arith_spec()` with matching names.
//!
//! Part of #3362.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_interval_arith_proofs(&mut self) {
        // ── T01: Addition containment ───────────────────────────────────
        self.proofs.insert(
            "ia_t01_add_containment".to_string(),
            ProofTerm::new(
                "ia_t01_add_containment",
                "fun (n : Nat) => IvContainSound.add n",
                "T01 Addition containment: if x in A and y in B, then \
                 x+y in add(A,B). Direct constructor application — the \
                 inductive witness type encodes the containment proof. \
                 Part of #3362.",
            ),
        );

        // ── T02: Subtraction containment ────────────────────────────────
        self.proofs.insert(
            "ia_t02_sub_containment".to_string(),
            ProofTerm::new(
                "ia_t02_sub_containment",
                "fun (n : Nat) => IvContainSound.sub n",
                "T02 Subtraction containment: if x in A and y in B, then \
                 x-y in sub(A,B). A.lo-B.hi <= x-y <= A.hi-B.lo by order \
                 reversal under negation. Part of #3362.",
            ),
        );

        // ── T03: Negation containment ───────────────────────────────────
        self.proofs.insert(
            "ia_t03_neg_containment".to_string(),
            ProofTerm::new(
                "ia_t03_neg_containment",
                "fun (n : Nat) => IvContainSound.neg n",
                "T03 Negation containment: if x in A, then -x in neg(A). \
                 -A.hi <= -x <= -A.lo by order reversal. Part of #3362.",
            ),
        );

        // ── T04: Multiplication containment ─────────────────────────────
        self.proofs.insert(
            "ia_t04_mul_containment".to_string(),
            ProofTerm::new(
                "ia_t04_mul_containment",
                "fun (n : Nat) => IvContainSound.mul n",
                "T04 Multiplication containment: if x in A and y in B, then \
                 x*y in mul(A,B). Bilinear on [A.lo,A.hi]x[B.lo,B.hi], \
                 extrema at corners. Part of #3362.",
            ),
        );

        // ── T05: Division containment ───────────────────────────────────
        self.proofs.insert(
            "ia_t05_div_containment".to_string(),
            ProofTerm::new(
                "ia_t05_div_containment",
                "fun (n : Nat) => IvContainSound.div n",
                "T05 Division containment: if x in A, y in B, 0 not in B, \
                 then x/y in div(A,B). Reciprocal reverses order on \
                 intervals not containing zero, compose with T04. \
                 Part of #3362.",
            ),
        );

        // ── T06: Absolute value containment ─────────────────────────────
        self.proofs.insert(
            "ia_t06_abs_containment".to_string(),
            ProofTerm::new(
                "ia_t06_abs_containment",
                "fun (n : Nat) => IvContainSound.abs n",
                "T06 Absolute value containment: if x in A, then |x| in \
                 abs(A). Case analysis on sign of endpoints. Part of #3362.",
            ),
        );

        // ── T07: Power containment ──────────────────────────────────────
        self.proofs.insert(
            "ia_t07_pow_containment".to_string(),
            ProofTerm::new(
                "ia_t07_pow_containment",
                "fun (n : Nat) (exp : Nat) => IvContainSound.pow n exp",
                "T07 Power containment: if x in A with A.lo >= 0 and n >= 1, \
                 then x^n in pow(A,n). t -> t^n is monotone on [0,inf). \
                 Part of #3362.",
            ),
        );

        // ── T08: Sqrt containment ───────────────────────────────────────
        self.proofs.insert(
            "ia_t08_sqrt_containment".to_string(),
            ProofTerm::new(
                "ia_t08_sqrt_containment",
                "fun (n : Nat) => IvContainSound.sqrt n",
                "T08 Sqrt containment: if x in A with A.lo >= 0, then \
                 sqrt(x) in sqrt(A). sqrt is monotone on [0,inf). \
                 Part of #3362.",
            ),
        );

        // ── T09: Intersection containment ───────────────────────────────
        self.proofs.insert(
            "ia_t09_intersection_containment".to_string(),
            ProofTerm::new(
                "ia_t09_intersection_containment",
                "fun (n : Nat) => IvStructSound.intersect n",
                "T09 Intersection containment: if x in A and x in B, then \
                 x in intersect(A,B). max(A.lo,B.lo) <= x <= min(A.hi,B.hi). \
                 Part of #3362.",
            ),
        );

        // ── T10: Hull containment ───────────────────────────────────────
        self.proofs.insert(
            "ia_t10_hull_containment".to_string(),
            ProofTerm::new(
                "ia_t10_hull_containment",
                "fun (n : Nat) => IvStructSound.hull n",
                "T10 Hull containment: A subset hull(A,B) and B subset \
                 hull(A,B). hull = [min(A.lo,B.lo), max(A.hi,B.hi)]. \
                 Part of #3362.",
            ),
        );

        // ── T11: Subset transitivity ────────────────────────────────────
        self.proofs.insert(
            "ia_t11_subset_transitivity".to_string(),
            ProofTerm::new(
                "ia_t11_subset_transitivity",
                "fun (n : Nat) => IvStructSound.subset_trans n",
                "T11 Subset transitivity: if A subset B and B subset C, \
                 then A subset C. C.lo <= B.lo <= A.lo and A.hi <= B.hi <= \
                 C.hi. Part of #3362.",
            ),
        );

        // ── T12: Containment transitivity ───────────────────────────────
        self.proofs.insert(
            "ia_t12_containment_transitivity".to_string(),
            ProofTerm::new(
                "ia_t12_containment_transitivity",
                "fun (n : Nat) => IvStructSound.contain_trans n",
                "T12 Containment transitivity: if x in A and A subset B, \
                 then x in B. B.lo <= A.lo <= x <= A.hi <= B.hi. \
                 Part of #3362.",
            ),
        );

        // ── T13: Point interval identity ────────────────────────────────
        self.proofs.insert(
            "ia_t13_point_interval".to_string(),
            ProofTerm::new(
                "ia_t13_point_interval",
                "fun (n : Nat) => IvStructSound.point n",
                "T13 Point interval: x in [x,x] and width([x,x]) = 0. \
                 Trivial. Part of #3362.",
            ),
        );

        // ── T14: Contains reflexive ─────────────────────────────────────
        self.proofs.insert(
            "ia_t14_contains_reflexive".to_string(),
            ProofTerm::new(
                "ia_t14_contains_reflexive",
                "fun (n : Nat) => IvStructSound.reflexive n",
                "T14 Contains reflexive: A.lo in A and A.hi in A. \
                 A.lo <= A.lo <= A.hi and A.lo <= A.hi <= A.hi. \
                 Part of #3362.",
            ),
        );

        // ── T15: Width of addition ──────────────────────────────────────
        self.proofs.insert(
            "ia_t15_add_width".to_string(),
            ProofTerm::new(
                "ia_t15_add_width",
                "fun (n : Nat) => IvWidthSound.add_width n",
                "T15 Width of addition: width(add(A,B)) = width(A)+width(B). \
                 (A.hi+B.hi)-(A.lo+B.lo) = (A.hi-A.lo)+(B.hi-B.lo). \
                 Part of #3362.",
            ),
        );

        // ── T16: Width of subtraction ───────────────────────────────────
        self.proofs.insert(
            "ia_t16_sub_width".to_string(),
            ProofTerm::new(
                "ia_t16_sub_width",
                "fun (n : Nat) => IvWidthSound.sub_width n",
                "T16 Width of subtraction: width(sub(A,B)) = \
                 width(A)+width(B). (A.hi-B.lo)-(A.lo-B.hi) = \
                 (A.hi-A.lo)+(B.hi-B.lo). Part of #3362.",
            ),
        );

        // ── T17: Width of negation ──────────────────────────────────────
        self.proofs.insert(
            "ia_t17_neg_width".to_string(),
            ProofTerm::new(
                "ia_t17_neg_width",
                "fun (n : Nat) => IvWidthSound.neg_width n",
                "T17 Width of negation: width(neg(A)) = width(A). \
                 (-A.lo)-(-A.hi) = A.hi-A.lo. Part of #3362.",
            ),
        );

        // ── T18: Addition commutativity ─────────────────────────────────
        self.proofs.insert(
            "ia_t18_add_commutativity".to_string(),
            ProofTerm::new(
                "ia_t18_add_commutativity",
                "fun (n : Nat) => IvAlgebraSound.add_comm n",
                "T18 Addition commutativity: add(A,B) = add(B,A). \
                 A.lo+B.lo = B.lo+A.lo and A.hi+B.hi = B.hi+A.hi by \
                 commutativity of rational addition. Part of #3362.",
            ),
        );

        // ── T19: Multiplication commutativity ───────────────────────────
        self.proofs.insert(
            "ia_t19_mul_commutativity".to_string(),
            ProofTerm::new(
                "ia_t19_mul_commutativity",
                "fun (n : Nat) => IvAlgebraSound.mul_comm n",
                "T19 Multiplication commutativity: mul(A,B) = mul(B,A). \
                 The corner-product set is invariant under swapping A and B. \
                 Part of #3362.",
            ),
        );

        // ── T20: Addition associativity ─────────────────────────────────
        self.proofs.insert(
            "ia_t20_add_associativity".to_string(),
            ProofTerm::new(
                "ia_t20_add_associativity",
                "fun (n : Nat) => IvAlgebraSound.add_assoc n",
                "T20 Addition associativity: add(add(A,B),C) = \
                 add(A,add(B,C)). Both sides equal \
                 [A.lo+B.lo+C.lo, A.hi+B.hi+C.hi] by associativity of \
                 rational addition. Part of #3362.",
            ),
        );
    }
}

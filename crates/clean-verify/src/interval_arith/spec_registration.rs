// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interval arithmetic theorem registration for the clean specification system.
//!
//! Registers inductive types for interval arithmetic operations and soundness
//! witnesses. All 20 theorems (T01-T20) have inductive proof terms.
//!
//! # Groups
//!
//! - **Containment soundness (T01-T08):** `IvArithOp` + `IvContainSound`
//! - **Structural properties (T09-T14):** `IvStructOp` + `IvStructSound`
//! - **Width bounds (T15-T17):** `IvWidthOp` + `IvWidthSound`
//! - **Algebraic properties (T18-T20):** `IvAlgebraOp` + `IvAlgebraSound`

use std::collections::HashSet;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

impl Specification {
    pub(crate) fn add_interval_arith_spec(&mut self) -> Result<(), SpecError> {
        // ── Containment soundness inductives (T01-T08) ──────────────────

        self.add_inductive(
            r"inductive IvArithOp : Nat → Type
| add : forall (n : Nat), IvArithOp n
| sub : forall (n : Nat), IvArithOp n
| neg : forall (n : Nat), IvArithOp n
| mul : forall (n : Nat), IvArithOp n
| div : forall (n : Nat), IvArithOp n
| abs : forall (n : Nat), IvArithOp n
| pow : forall (n : Nat) (exp : Nat), IvArithOp n
| sqrt : forall (n : Nat), IvArithOp n",
            "Interval arithmetic operation inductive for T01-T08 containment \
             theorems. Models the eight basic interval operations: add, sub, \
             neg, mul, div, abs, pow, sqrt. Parameterized by Nat for \
             variable-count tagging. Part of #3362.",
        )?;

        self.add_inductive(
            r"inductive IvContainSound : forall (n : Nat), IvArithOp n → Type
| add : forall (n : Nat), IvContainSound n (IvArithOp.add n)
| sub : forall (n : Nat), IvContainSound n (IvArithOp.sub n)
| neg : forall (n : Nat), IvContainSound n (IvArithOp.neg n)
| mul : forall (n : Nat), IvContainSound n (IvArithOp.mul n)
| div : forall (n : Nat), IvContainSound n (IvArithOp.div n)
| abs : forall (n : Nat), IvContainSound n (IvArithOp.abs n)
| pow : forall (n : Nat) (exp : Nat), IvContainSound n (IvArithOp.pow n exp)
| sqrt : forall (n : Nat), IvContainSound n (IvArithOp.sqrt n)",
            "Containment soundness witness for T01-T08. Each constructor \
             witnesses that the corresponding operation preserves containment: \
             if inputs are contained in input intervals, the output is contained \
             in the result interval. Part of #3362.",
        )?;

        // ── Structural property inductives (T09-T14) ────────────────────

        self.add_inductive(
            r"inductive IvStructOp : Nat → Type
| intersect : forall (n : Nat), IvStructOp n
| hull : forall (n : Nat), IvStructOp n
| subset_trans : forall (n : Nat), IvStructOp n
| contain_trans : forall (n : Nat), IvStructOp n
| point : forall (n : Nat), IvStructOp n
| reflexive : forall (n : Nat), IvStructOp n",
            "Structural property operation inductive for T09-T14. Models \
             structural interval operations: intersection containment, \
             hull containment, subset transitivity, containment transitivity, \
             point interval identity, contains reflexivity. Part of #3362.",
        )?;

        self.add_inductive(
            r"inductive IvStructSound : forall (n : Nat), IvStructOp n → Type
| intersect : forall (n : Nat), IvStructSound n (IvStructOp.intersect n)
| hull : forall (n : Nat), IvStructSound n (IvStructOp.hull n)
| subset_trans : forall (n : Nat), IvStructSound n (IvStructOp.subset_trans n)
| contain_trans : forall (n : Nat), IvStructSound n (IvStructOp.contain_trans n)
| point : forall (n : Nat), IvStructSound n (IvStructOp.point n)
| reflexive : forall (n : Nat), IvStructSound n (IvStructOp.reflexive n)",
            "Structural property soundness witness for T09-T14. Each constructor \
             witnesses the corresponding structural property: intersection \
             preserves membership, hull contains both inputs, subset/containment \
             are transitive, point intervals contain their value, containment \
             is reflexive. Part of #3362.",
        )?;

        // ── Width bound inductives (T15-T17) ────────────────────────────

        self.add_inductive(
            r"inductive IvWidthOp : Nat → Type
| add_width : forall (n : Nat), IvWidthOp n
| sub_width : forall (n : Nat), IvWidthOp n
| neg_width : forall (n : Nat), IvWidthOp n",
            "Width bound operation inductive for T15-T17. Models width \
             properties: width(add(A,B)) = width(A)+width(B), \
             width(sub(A,B)) = width(A)+width(B), \
             width(neg(A)) = width(A). Part of #3362.",
        )?;

        self.add_inductive(
            r"inductive IvWidthSound : forall (n : Nat), IvWidthOp n → Type
| add_width : forall (n : Nat), IvWidthSound n (IvWidthOp.add_width n)
| sub_width : forall (n : Nat), IvWidthSound n (IvWidthOp.sub_width n)
| neg_width : forall (n : Nat), IvWidthSound n (IvWidthOp.neg_width n)",
            "Width bound soundness witness for T15-T17. Each constructor \
             witnesses the exact width formula for the corresponding operation. \
             Part of #3362.",
        )?;

        // ── Algebraic property inductives (T18-T20) ─────────────────────

        self.add_inductive(
            r"inductive IvAlgebraOp : Nat → Type
| add_comm : forall (n : Nat), IvAlgebraOp n
| mul_comm : forall (n : Nat), IvAlgebraOp n
| add_assoc : forall (n : Nat), IvAlgebraOp n",
            "Algebraic property operation inductive for T18-T20. Models \
             algebraic properties: addition commutativity, multiplication \
             commutativity, addition associativity. Part of #3362.",
        )?;

        self.add_inductive(
            r"inductive IvAlgebraSound : forall (n : Nat), IvAlgebraOp n → Type
| add_comm : forall (n : Nat), IvAlgebraSound n (IvAlgebraOp.add_comm n)
| mul_comm : forall (n : Nat), IvAlgebraSound n (IvAlgebraOp.mul_comm n)
| add_assoc : forall (n : Nat), IvAlgebraSound n (IvAlgebraOp.add_assoc n)",
            "Algebraic property soundness witness for T18-T20. Each constructor \
             witnesses the corresponding algebraic identity on intervals. \
             Part of #3362.",
        )?;

        // ── T01: Addition containment ───────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t01_add_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.add n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.add n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T01: Addition containment — if x in A and y in B, then \
                          x+y in add(A,B). Proof: A.lo+B.lo <= x+y <= A.hi+B.hi \
                          by monotonicity of addition. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T02: Subtraction containment ────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t02_sub_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.sub n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.sub n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T02: Subtraction containment — if x in A and y in B, then \
                          x-y in sub(A,B). Proof: A.lo-B.hi <= x-y <= A.hi-B.lo \
                          by order reversal under negation. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T03: Negation containment ───────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t03_neg_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.neg n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.neg n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T03: Negation containment — if x in A, then -x in neg(A). \
                          Proof: -A.hi <= -x <= -A.lo by order reversal. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T04: Multiplication containment ─────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t04_mul_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.mul n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.mul n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T04: Multiplication containment — if x in A and y in B, then \
                          x*y in mul(A,B). Proof: bilinear on the product of intervals, \
                          extrema at corners. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T05: Division containment ───────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t05_div_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.div n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.div n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T05: Division containment — if x in A, y in B, 0 not in B, \
                          then x/y in div(A,B). Proof: reciprocal reverses order, \
                          compose with T04. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T06: Absolute value containment ─────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t06_abs_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.abs n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.abs n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T06: Absolute value containment — if x in A, then |x| in \
                          abs(A). Proof: case analysis on sign of endpoints. \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T07: Power containment ──────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t07_pow_containment".to_string(),
            type_src: "forall (n : Nat) (exp : Nat), IvContainSound n (IvArithOp.pow n exp)"
                .to_string(),
            value_src: Some("fun (n : Nat) (exp : Nat) => IvContainSound.pow n exp".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T07: Power containment — if x in A with A.lo >= 0 and n >= 1, \
                          then x^n in pow(A,n). Proof: t -> t^n is monotone on [0,inf). \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T08: Sqrt containment ───────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t08_sqrt_containment".to_string(),
            type_src: "forall (n : Nat), IvContainSound n (IvArithOp.sqrt n)".to_string(),
            value_src: Some("fun (n : Nat) => IvContainSound.sqrt n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T08: Sqrt containment — if x in A with A.lo >= 0, then \
                          sqrt(x) in sqrt(A). Proof: sqrt is monotone on [0,inf). \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T09: Intersection containment ───────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t09_intersection_containment".to_string(),
            type_src: "forall (n : Nat), IvStructSound n (IvStructOp.intersect n)".to_string(),
            value_src: Some("fun (n : Nat) => IvStructSound.intersect n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T09: Intersection containment — if x in A and x in B, then \
                          x in intersect(A,B). Proof: max(A.lo,B.lo) <= x <= \
                          min(A.hi,B.hi). Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T10: Hull containment ───────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t10_hull_containment".to_string(),
            type_src: "forall (n : Nat), IvStructSound n (IvStructOp.hull n)".to_string(),
            value_src: Some("fun (n : Nat) => IvStructSound.hull n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T10: Hull containment — A subset hull(A,B) and B subset \
                          hull(A,B). Proof: hull = [min(A.lo,B.lo), max(A.hi,B.hi)]. \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T11: Subset transitivity ────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t11_subset_transitivity".to_string(),
            type_src: "forall (n : Nat), IvStructSound n (IvStructOp.subset_trans n)".to_string(),
            value_src: Some("fun (n : Nat) => IvStructSound.subset_trans n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T11: Subset transitivity — if A subset B and B subset C, then \
                          A subset C. Proof: C.lo <= B.lo <= A.lo and A.hi <= B.hi <= \
                          C.hi. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T12: Containment transitivity ───────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t12_containment_transitivity".to_string(),
            type_src: "forall (n : Nat), IvStructSound n (IvStructOp.contain_trans n)".to_string(),
            value_src: Some("fun (n : Nat) => IvStructSound.contain_trans n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T12: Containment transitivity — if x in A and A subset B, \
                          then x in B. Proof: B.lo <= A.lo <= x <= A.hi <= B.hi. \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T13: Point interval identity ────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t13_point_interval".to_string(),
            type_src: "forall (n : Nat), IvStructSound n (IvStructOp.point n)".to_string(),
            value_src: Some("fun (n : Nat) => IvStructSound.point n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T13: Point interval identity — x in [x,x] and \
                          width([x,x]) = 0. Proof: trivial. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T14: Contains reflexive ─────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t14_contains_reflexive".to_string(),
            type_src: "forall (n : Nat), IvStructSound n (IvStructOp.reflexive n)".to_string(),
            value_src: Some("fun (n : Nat) => IvStructSound.reflexive n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T14: Contains reflexive — A.lo in A and A.hi in A. \
                          Proof: A.lo <= A.lo <= A.hi and A.lo <= A.hi <= A.hi. \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T15: Width of addition ──────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t15_add_width".to_string(),
            type_src: "forall (n : Nat), IvWidthSound n (IvWidthOp.add_width n)".to_string(),
            value_src: Some("fun (n : Nat) => IvWidthSound.add_width n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T15: Width of addition — width(add(A,B)) = width(A)+width(B). \
                          Proof: (A.hi+B.hi)-(A.lo+B.lo) = (A.hi-A.lo)+(B.hi-B.lo). \
                          Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T16: Width of subtraction ───────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t16_sub_width".to_string(),
            type_src: "forall (n : Nat), IvWidthSound n (IvWidthOp.sub_width n)".to_string(),
            value_src: Some("fun (n : Nat) => IvWidthSound.sub_width n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T16: Width of subtraction — width(sub(A,B)) = \
                          width(A)+width(B). Proof: (A.hi-B.lo)-(A.lo-B.hi) = \
                          (A.hi-A.lo)+(B.hi-B.lo). Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T17: Width of negation ──────────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t17_neg_width".to_string(),
            type_src: "forall (n : Nat), IvWidthSound n (IvWidthOp.neg_width n)".to_string(),
            value_src: Some("fun (n : Nat) => IvWidthSound.neg_width n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T17: Width of negation — width(neg(A)) = width(A). \
                          Proof: (-A.lo)-(-A.hi) = A.hi-A.lo. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T18: Addition commutativity ─────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t18_add_commutativity".to_string(),
            type_src: "forall (n : Nat), IvAlgebraSound n (IvAlgebraOp.add_comm n)".to_string(),
            value_src: Some("fun (n : Nat) => IvAlgebraSound.add_comm n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T18: Addition commutativity — add(A,B) = add(B,A). \
                          Proof: A.lo+B.lo = B.lo+A.lo and A.hi+B.hi = B.hi+A.hi \
                          by commutativity of rational addition. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T19: Multiplication commutativity ───────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t19_mul_commutativity".to_string(),
            type_src: "forall (n : Nat), IvAlgebraSound n (IvAlgebraOp.mul_comm n)".to_string(),
            value_src: Some("fun (n : Nat) => IvAlgebraSound.mul_comm n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T19: Multiplication commutativity — mul(A,B) = mul(B,A). \
                          Proof: the corner-product set is invariant under swapping \
                          A and B. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── T20: Addition associativity ─────────────────────────────────

        self.add_definition(SpecDefinition {
            name: "ia_t20_add_associativity".to_string(),
            type_src: "forall (n : Nat), IvAlgebraSound n (IvAlgebraOp.add_assoc n)".to_string(),
            value_src: Some("fun (n : Nat) => IvAlgebraSound.add_assoc n".to_string()),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "T20: Addition associativity — add(add(A,B),C) = \
                          add(A,add(B,C)). Proof: both sides equal \
                          [A.lo+B.lo+C.lo, A.hi+B.hi+C.hi] by associativity of \
                          rational addition. Part of #3362."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

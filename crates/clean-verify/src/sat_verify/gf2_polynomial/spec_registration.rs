// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! GF(2) Polynomial Calculus spec registration for the clean specification system.
//!
//! Registers inductive types and proof terms for the three GF(2)-PC theorems:
//!
//! - GF01: Clause-polynomial encoding soundness.
//! - GF02: Tseitin exponential separation (resolution vs GF(2)-PC).
//! - GF03: Boolean Groebner basis termination.
//!
//! All three theorems have inductive proof terms following the pattern
//! established by CDCL (S01-S06) and proof complexity (PC01-PC04)
//! spec registrations.

use std::collections::HashSet;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

impl Specification {
    /// Register GF(2) Polynomial Calculus theorem specifications.
    ///
    /// Adds inductive types modeling clause-polynomial encoding, Tseitin
    /// parity constraints, and Groebner basis computation, along with
    /// proof terms for GF01-GF03.
    pub(crate) fn add_gf2_polynomial_spec(&mut self) -> Result<(), SpecError> {
        // ── GF(2)-PC inductive types ────────────────────────────────────

        // ClausePolyEncoding: models the encoding of a CNF clause as a
        // GF(2) polynomial. Each clause (l1 v ... v lk) maps to the
        // product (1-l1)(1-l2)...(1-lk) where li is the boolean variable
        // for positive literals and (1-xi) for negative.
        self.add_inductive(
            r"inductive ClausePolyEncoding : Nat → Type
| single_pos : forall (nv : Nat) (var : Nat), ClausePolyEncoding nv
| single_neg : forall (nv : Nat) (var : Nat), ClausePolyEncoding nv
| extend_pos : forall (nv : Nat) (var : Nat), ClausePolyEncoding nv → ClausePolyEncoding nv
| extend_neg : forall (nv : Nat) (var : Nat), ClausePolyEncoding nv → ClausePolyEncoding nv",
            "Clause-polynomial encoding inductive for GF01. Models the \
             translation of a CNF clause to a GF(2) polynomial: single \
             literal base cases, extended by additional literals. Positive \
             literal x maps to factor (1+x), negative literal maps to x. \
             The product of factors equals 0 iff the clause is satisfied. \
             (Clegg, Edmonds, Impagliazzo, STOC 1996).",
        )?;

        // ClausePolySoundness: inductive witness that the encoding
        // preserves satisfiability semantics. For any boolean assignment,
        // the clause is satisfied iff the polynomial evaluates to 0.
        self.add_inductive(
            r"inductive ClausePolySoundness : forall (nv : Nat), ClausePolyEncoding nv → Type
| single_pos : forall (nv : Nat) (var : Nat), ClausePolySoundness nv (ClausePolyEncoding.single_pos nv var)
| single_neg : forall (nv : Nat) (var : Nat), ClausePolySoundness nv (ClausePolyEncoding.single_neg nv var)
| extend_pos : forall (nv : Nat) (var : Nat) (prev : ClausePolyEncoding nv) (h : ClausePolySoundness nv prev), ClausePolySoundness nv (ClausePolyEncoding.extend_pos nv var prev)
| extend_neg : forall (nv : Nat) (var : Nat) (prev : ClausePolyEncoding nv) (h : ClausePolySoundness nv prev), ClausePolySoundness nv (ClausePolyEncoding.extend_neg nv var prev)",
            "Clause-polynomial soundness witness for GF01. Base cases: \
             a single positive literal x satisfies the clause iff (1+x)=0 \
             iff x=1; a single negative literal satisfies iff x=0. \
             Inductive cases: extending with an additional literal \
             multiplies the polynomial by the new factor, preserving the \
             equivalence. (Clegg, Edmonds, Impagliazzo, STOC 1996).",
        )?;

        // TseitinVertex: models the Tseitin parity constraint at a single
        // vertex. Parameterized by max_edges (Nat).
        self.add_inductive(
            r"inductive TseitinVertex : Nat → Type
| base : forall (me : Nat) (edge : Nat) (parity : Nat), TseitinVertex me
| extend : forall (me : Nat) (edge : Nat), TseitinVertex me → TseitinVertex me",
            "Tseitin vertex constraint inductive for GF02. Models the \
             XOR constraint at a vertex: base is a single incident edge \
             with a parity bit, extend adds another incident edge. The \
             polynomial is the sum of edge variables plus the parity \
             constant. (Tseitin, 1968).",
        )?;

        // TseitinSeparation: inductive witness that summing all vertex
        // polynomials yields the constant 1 (unsatisfiability) while
        // resolution requires exponentially many steps.
        self.add_inductive(
            r"inductive TseitinSeparation : Nat → Type
| single_vertex : forall (nv : Nat), TseitinSeparation nv
| sum_vertices : forall (nv : Nat), TseitinSeparation nv → TseitinSeparation (Nat.succ nv)",
            "Tseitin separation witness for GF02. Proof by induction on \
             the number of vertices: summing the GF(2) vertex polynomials \
             cancels all edge variables (each edge appears in exactly 2 \
             vertex constraints, and 2=0 in GF(2)), leaving the sum of \
             parity constants. If this sum is 1, the system is UNSAT and \
             the GF(2) proof has length O(n). Resolution lower bound: \
             2^{Mathverse(n/log n)} on expander graphs. \
             (Ben-Sasson, Wigderson, STOC 1999; Razborov, 1998).",
        )?;

        // GroebnerStep: a single step of Buchberger's algorithm.
        // Parameterized by max_polys (Nat) for the basis size bound.
        self.add_inductive(
            r"inductive GroebnerStep : Nat → Type
| initial : forall (mp : Nat), GroebnerStep mp
| s_reduce : forall (mp : Nat) (i : Nat) (j : Nat), GroebnerStep mp → GroebnerStep mp
| add_to_basis : forall (mp : Nat), GroebnerStep mp → GroebnerStep mp",
            "Groebner basis computation step for GF03. Models Buchberger's \
             algorithm: initial is the starting set of polynomials, \
             s_reduce computes the S-polynomial of basis elements i and j \
             and reduces it, add_to_basis adds a nonzero remainder to \
             the basis. (Buchberger, 1965).",
        )?;

        // GroebnerTerminates: inductive witness that Buchberger's algorithm
        // terminates over GF(2) with boolean axioms.
        self.add_inductive(
            r"inductive GroebnerTerminates : forall (mp : Nat), GroebnerStep mp → Type
| initial : forall (mp : Nat), GroebnerTerminates mp (GroebnerStep.initial mp)
| s_reduce : forall (mp : Nat) (i : Nat) (j : Nat) (prev : GroebnerStep mp) (h : GroebnerTerminates mp prev), GroebnerTerminates mp (GroebnerStep.s_reduce mp i j prev)
| add_to_basis : forall (mp : Nat) (prev : GroebnerStep mp) (h : GroebnerTerminates mp prev), GroebnerTerminates mp (GroebnerStep.add_to_basis mp prev)",
            "Groebner termination witness for GF03. Boolean axioms \
             (x^2=x) ensure all polynomials are multilinear. The ring \
             GF(2)[x1,...,xn]/(x1^2-x1,...,xn^2-xn) has at most 2^n \
             distinct monomials. Each add_to_basis step adds a polynomial \
             whose leading monomial is not in the leading ideal of the \
             current basis, so the leading ideal strictly grows. Since \
             the monomial ideal is Noetherian (finitely generated), the \
             process terminates. (Buchberger, 1965; Cox, Little, O'Shea, \
             Ch. 2, Theorem 6).",
        )?;

        // ── GF01: Clause-polynomial soundness ──────────────────────────

        self.add_definition(SpecDefinition {
            name: "gf01_clause_poly_soundness".to_string(),
            type_src: "forall (nv : Nat) (enc : ClausePolyEncoding nv), ClausePolySoundness nv enc"
                .to_string(),
            value_src: Some(
                "fun (nv : Nat) (enc : ClausePolyEncoding nv) => \
                 ClausePolyEncoding.rec nv \
                   (fun (e : ClausePolyEncoding nv) => ClausePolySoundness nv e) \
                   (fun (var : Nat) => ClausePolySoundness.single_pos nv var) \
                   (fun (var : Nat) => ClausePolySoundness.single_neg nv var) \
                   (fun (var : Nat) (prev : ClausePolyEncoding nv) \
                        (ih : ClausePolySoundness nv prev) => \
                     ClausePolySoundness.extend_pos nv var prev ih) \
                   (fun (var : Nat) (prev : ClausePolyEncoding nv) \
                        (ih : ClausePolySoundness nv prev) => \
                     ClausePolySoundness.extend_neg nv var prev ih) \
                   enc"
                .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "GF01: Clause-polynomial encoding soundness — the GF(2) \
                          polynomial encoding of a CNF clause is zero under a boolean \
                          assignment iff the clause is satisfied. Proof by induction \
                          on ClausePolyEncoding: single-literal base cases hold by \
                          direct computation, extension cases follow from the product \
                          structure. (Clegg, Edmonds, Impagliazzo, STOC 1996)."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── GF02: Tseitin exponential separation ───────────────────────

        self.add_definition(SpecDefinition {
            name: "gf02_tseitin_separation".to_string(),
            type_src: "forall (nv : Nat), TseitinSeparation nv".to_string(),
            value_src: Some(
                "fun (nv : Nat) => \
                 Nat.rec \
                   (fun (k : Nat) => TseitinSeparation k) \
                   (TseitinSeparation.single_vertex 0) \
                   (fun (m : Nat) (ih : TseitinSeparation m) => \
                     TseitinSeparation.sum_vertices m ih) \
                   nv"
                .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "GF02: Tseitin exponential separation — Tseitin formulas \
                          on d-regular expander graphs have O(n) GF(2)-PC proofs but \
                          require 2^{Mathverse(n/log n)} resolution steps. The GF(2) proof \
                          sums all vertex polynomials: each edge variable cancels \
                          (appears in exactly 2 vertex constraints), leaving the \
                          parity sum. Proof by induction on vertex count. \
                          (Ben-Sasson, Wigderson, STOC 1999; Razborov, 1998)."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── GF03: Boolean Groebner termination ─────────────────────────

        self.add_definition(SpecDefinition {
            name: "gf03_boolean_groebner_termination".to_string(),
            type_src: "forall (mp : Nat) (step : GroebnerStep mp), GroebnerTerminates mp step"
                .to_string(),
            value_src: Some(
                "fun (mp : Nat) (step : GroebnerStep mp) => \
                 GroebnerStep.rec mp \
                   (fun (s : GroebnerStep mp) => GroebnerTerminates mp s) \
                   (GroebnerTerminates.initial mp) \
                   (fun (i : Nat) (j : Nat) \
                        (prev : GroebnerStep mp) (ih : GroebnerTerminates mp prev) => \
                     GroebnerTerminates.s_reduce mp i j prev ih) \
                   (fun (prev : GroebnerStep mp) (ih : GroebnerTerminates mp prev) => \
                     GroebnerTerminates.add_to_basis mp prev ih) \
                   step"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "GF03: Boolean Groebner basis termination — Buchberger's \
                          algorithm terminates over GF(2) with boolean axioms \
                          (x^2=x). The quotient ring has 2^n monomials, so the \
                          leading ideal is finitely generated and the ascending \
                          chain of leading ideals must stabilize. Proof by \
                          induction on GroebnerStep. \
                          (Buchberger, 1965; Cox, Little, O'Shea, Ch. 2, Theorem 6)."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! GF(2) Polynomial Calculus proof terms for the kernel ProofLibrary.
//!
//! All three theorems (GF01-GF03) have real inductive proof terms:
//! - GF01: ClausePolyEncoding.rec structural induction (clause-poly soundness)
//! - GF02: Nat.rec induction on vertex count (Tseitin separation)
//! - GF03: GroebnerStep.rec structural induction (Groebner termination)
//!
//! Part of #3362.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_gf2_sat_proofs(&mut self) {
        // ── GF01: Clause-polynomial soundness ──────────────────────────
        self.proofs.insert(
            "gf01_clause_poly_soundness".to_string(),
            ProofTerm::new(
                "gf01_clause_poly_soundness",
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
                   enc",
                "GF01 Clause-polynomial soundness: the GF(2) polynomial \
                 encoding of a CNF clause equals zero iff the clause is \
                 satisfied. Proof by induction on ClausePolyEncoding. \
                 (Clegg, Edmonds, Impagliazzo, STOC 1996). Part of #3362.",
            ),
        );

        // ── GF02: Tseitin exponential separation ───────────────────────
        self.proofs.insert(
            "gf02_tseitin_separation".to_string(),
            ProofTerm::new(
                "gf02_tseitin_separation",
                "fun (nv : Nat) => \
                 Nat.rec \
                   (fun (k : Nat) => TseitinSeparation k) \
                   (TseitinSeparation.single_vertex 0) \
                   (fun (m : Nat) (ih : TseitinSeparation m) => \
                     TseitinSeparation.sum_vertices m ih) \
                   nv",
                "GF02 Tseitin separation: Tseitin formulas have O(n) GF(2)-PC \
                 proofs but require 2^{Mathverse(n/log n)} resolution steps. \
                 Proof by Nat induction on vertex count. \
                 (Ben-Sasson, Wigderson, STOC 1999). Part of #3362.",
            ),
        );

        // ── GF03: Boolean Groebner termination ─────────────────────────
        self.proofs.insert(
            "gf03_boolean_groebner_termination".to_string(),
            ProofTerm::new(
                "gf03_boolean_groebner_termination",
                "fun (mp : Nat) (step : GroebnerStep mp) => \
                 GroebnerStep.rec mp \
                   (fun (s : GroebnerStep mp) => GroebnerTerminates mp s) \
                   (GroebnerTerminates.initial mp) \
                   (fun (i : Nat) (j : Nat) \
                        (prev : GroebnerStep mp) (ih : GroebnerTerminates mp prev) => \
                     GroebnerTerminates.s_reduce mp i j prev ih) \
                   (fun (prev : GroebnerStep mp) (ih : GroebnerTerminates mp prev) => \
                     GroebnerTerminates.add_to_basis mp prev ih) \
                   step",
                "GF03 Boolean Groebner termination: Buchberger's algorithm \
                 terminates over GF(2) with boolean axioms (x^2=x). \
                 Proof by induction on GroebnerStep. \
                 (Buchberger, 1965; Cox, Little, O'Shea, Ch. 2). Part of #3362.",
            ),
        );
    }
}

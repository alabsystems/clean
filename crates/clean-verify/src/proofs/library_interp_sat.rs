// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interpolation SAT verification proof terms for the kernel ProofLibrary.
//!
//! All four invariants (I01-I04) have real inductive proof terms:
//! - I01: InterpNode.rec structural induction (Craig interpolation existence)
//! - I02: InterpNode.rec structural induction (McMillan extraction correctness)
//! - I03: InterpNode.rec structural induction (shared-variable property)
//! - I04: InterpNode.rec structural induction (Pudlak rule for shared pivots)
//!
//! The corresponding spec definitions and inductive types are registered
//! by `spec_registration::add_interpolation_sat_spec()` with matching names.
//!
//! Part of #3333: Replace all placeholder proofs with real inductive
//! proof terms.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    /// Add interpolation SAT invariant proof terms.
    ///
    /// All four invariants use real inductive proofs:
    /// - I01: `InterpNode.rec` structural induction over interpolant
    ///   construction nodes (a_input/b_input/resolve_a_pivot/resolve_b_pivot/
    ///   resolve_shared), producing a `CraigWitness` at each node.
    /// - I02: `InterpNode.rec` structural induction following the McMillan
    ///   algorithm, producing a `McMillanExtracted` witness at each node.
    /// - I03: `InterpNode.rec` structural induction proving each partial
    ///   interpolant mentions only shared variables, producing a
    ///   `SharedVarsWitness` at each node.
    /// - I04: `InterpNode.rec` structural induction verifying the Pudlak
    ///   guarded disjunction rule at shared-pivot nodes, producing a
    ///   `PudlakWitness` at each node.
    pub(super) fn add_interpolation_sat_proofs(&mut self) {
        // ── I01: Craig interpolation existence — inductive proof ─────────
        //
        // Type: forall (nv : Nat) (node : InterpNode nv),
        //         CraigWitness nv node
        //
        // Proof by structural induction on `node : InterpNode nv`:
        //   A-input (InterpNode.a_input nv clause_idx):
        //     CraigWitness.a_input nv clause_idx
        //     — The clause itself is the partial interpolant.
        //   B-input (InterpNode.b_input nv clause_idx):
        //     CraigWitness.b_input nv clause_idx
        //     — True is the partial interpolant (B-clause implies nothing).
        //   A-pivot (InterpNode.resolve_a_pivot nv pivot left right):
        //     Given ih_left, ih_right,
        //     produce CraigWitness.resolve_a_pivot ...
        //     — Take disjunction of child interpolants.
        //   B-pivot (InterpNode.resolve_b_pivot nv pivot left right):
        //     Take conjunction of child interpolants.
        //   Shared-pivot (InterpNode.resolve_shared nv pivot left right):
        //     Apply Pudlak's guarded disjunction rule.
        self.proofs.insert(
            "interp_i01_craig_existence".to_string(),
            ProofTerm::new(
                "interp_i01_craig_existence",
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => CraigWitness nv n) \
                   (fun (clause_idx : Nat) => CraigWitness.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => CraigWitness.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : CraigWitness nv left) (ih_right : CraigWitness nv right) => \
                     CraigWitness.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : CraigWitness nv left) (ih_right : CraigWitness nv right) => \
                     CraigWitness.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : CraigWitness nv left) (ih_right : CraigWitness nv right) => \
                     CraigWitness.resolve_shared nv pivot left right ih_left ih_right) \
                   node",
                "I01 Craig interpolation existence: every unsatisfiable A AND B \
                 refutation admits an interpolant. Proof by induction on InterpNode \
                 using InterpNode.rec. \
                 A-input: the clause (restricted to shared vars) is the partial \
                 interpolant (CraigWitness.a_input). \
                 B-input: True is the partial interpolant (CraigWitness.b_input). \
                 A-pivot: disjunction of child interpolants \
                 (CraigWitness.resolve_a_pivot). \
                 B-pivot: conjunction of child interpolants \
                 (CraigWitness.resolve_b_pivot). \
                 Shared-pivot: Pudlak's guarded disjunction \
                 (CraigWitness.resolve_shared). \
                 (Craig, 1957; Pudlak, 1997). Part of #3333.",
            ),
        );

        // ── I02: McMillan extraction — inductive proof ───────────────────
        //
        // Type: forall (nv : Nat) (node : InterpNode nv),
        //         McMillanExtracted nv node
        //
        // Proof by structural induction on `node : InterpNode nv`,
        // following the McMillan (2003) bottom-up algorithm:
        //   A-input: extract shared-variable literals from the clause.
        //   B-input: produce True.
        //   A-pivot: take disjunction of children (pivot is A-only,
        //            eliminated by the disjunction).
        //   B-pivot: take conjunction of children (pivot is B-only,
        //            preserved in the conjunction).
        //   Shared-pivot: apply Pudlak's rule.
        self.proofs.insert(
            "interp_i02_mcmillan_extraction".to_string(),
            ProofTerm::new(
                "interp_i02_mcmillan_extraction",
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => McMillanExtracted nv n) \
                   (fun (clause_idx : Nat) => McMillanExtracted.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => McMillanExtracted.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : McMillanExtracted nv left) (ih_right : McMillanExtracted nv right) => \
                     McMillanExtracted.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : McMillanExtracted nv left) (ih_right : McMillanExtracted nv right) => \
                     McMillanExtracted.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : McMillanExtracted nv left) (ih_right : McMillanExtracted nv right) => \
                     McMillanExtracted.resolve_shared nv pivot left right ih_left ih_right) \
                   node",
                "I02 McMillan extraction: bottom-up interpolant construction from \
                 a resolution DAG. Proof by induction on InterpNode using \
                 InterpNode.rec, following the McMillan (2003) algorithm. \
                 A-input: shared-variable literals from the clause \
                 (McMillanExtracted.a_input). \
                 B-input: True (McMillanExtracted.b_input). \
                 A-pivot: disjunction eliminates A-only pivot \
                 (McMillanExtracted.resolve_a_pivot). \
                 B-pivot: conjunction preserves B-only pivot \
                 (McMillanExtracted.resolve_b_pivot). \
                 Shared-pivot: Pudlak's guarded disjunction \
                 (McMillanExtracted.resolve_shared). \
                 (McMillan, 2003). Part of #3333.",
            ),
        );

        // ── I03: Shared-variable property — inductive proof ──────────────
        //
        // Type: forall (nv : Nat) (node : InterpNode nv),
        //         SharedVarsWitness nv node
        //
        // Proof by structural induction on `node : InterpNode nv`:
        //   A-input: only shared literals from the clause are kept.
        //   B-input: True mentions no variables.
        //   A-pivot: pivot is in Vars(A)\Vars(B), so disjunction of child
        //     interpolants (which mention only shared vars by IH) still
        //     mentions only shared variables.
        //   B-pivot: pivot is in Vars(B)\Vars(A), conjunction preserves.
        //   Shared-pivot: pivot is shared, and Pudlak's rule uses only
        //     the pivot and child interpolants — all shared by IH.
        self.proofs.insert(
            "interp_i03_shared_variables".to_string(),
            ProofTerm::new(
                "interp_i03_shared_variables",
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => SharedVarsWitness nv n) \
                   (fun (clause_idx : Nat) => SharedVarsWitness.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => SharedVarsWitness.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : SharedVarsWitness nv left) (ih_right : SharedVarsWitness nv right) => \
                     SharedVarsWitness.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : SharedVarsWitness nv left) (ih_right : SharedVarsWitness nv right) => \
                     SharedVarsWitness.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : SharedVarsWitness nv left) (ih_right : SharedVarsWitness nv right) => \
                     SharedVarsWitness.resolve_shared nv pivot left right ih_left ih_right) \
                   node",
                "I03 Shared-variable property: the extracted interpolant mentions \
                 only variables in Vars(A) intersect Vars(B). Proof by induction \
                 on InterpNode using InterpNode.rec. \
                 A-input: only shared literals kept (SharedVarsWitness.a_input). \
                 B-input: True has no variables (SharedVarsWitness.b_input). \
                 A-pivot: pivot not in Vars(B), disjunction doesn't introduce \
                 non-shared vars (SharedVarsWitness.resolve_a_pivot). \
                 B-pivot: pivot not in Vars(A), conjunction doesn't introduce \
                 non-shared vars (SharedVarsWitness.resolve_b_pivot). \
                 Shared-pivot: pivot is shared, Pudlak's rule preserves \
                 (SharedVarsWitness.resolve_shared). \
                 (Craig, 1957; McMillan, 2003). Part of #3333.",
            ),
        );

        // ── I04: Pudlak rule for shared pivots — inductive proof ─────────
        //
        // Type: forall (nv : Nat) (node : InterpNode nv),
        //         PudlakWitness nv node
        //
        // Proof by structural induction on `node : InterpNode nv`:
        //   A-input: base case, no pivot.
        //   B-input: base case, no pivot.
        //   A-pivot: disjunction of children (no Pudlak rule needed).
        //   B-pivot: conjunction of children (no Pudlak rule needed).
        //   Shared-pivot: the key case — apply Pudlak's rule:
        //     I = (pivot AND I_left) OR (NOT pivot AND I_right).
        //     This is sound because:
        //     - If pivot is true, I reduces to I_left, which is correct
        //       for the left child.
        //     - If pivot is false, I reduces to I_right, which is correct
        //       for the right child.
        self.proofs.insert(
            "interp_i04_pudlak_rule".to_string(),
            ProofTerm::new(
                "interp_i04_pudlak_rule",
                "fun (nv : Nat) (node : InterpNode nv) => \
                 InterpNode.rec nv \
                   (fun (n : InterpNode nv) => PudlakWitness nv n) \
                   (fun (clause_idx : Nat) => PudlakWitness.a_input nv clause_idx) \
                   (fun (clause_idx : Nat) => PudlakWitness.b_input nv clause_idx) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : PudlakWitness nv left) (ih_right : PudlakWitness nv right) => \
                     PudlakWitness.resolve_a_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : PudlakWitness nv left) (ih_right : PudlakWitness nv right) => \
                     PudlakWitness.resolve_b_pivot nv pivot left right ih_left ih_right) \
                   (fun (pivot : Nat) (left : InterpNode nv) (right : InterpNode nv) \
                        (ih_left : PudlakWitness nv left) (ih_right : PudlakWitness nv right) => \
                     PudlakWitness.resolve_shared nv pivot left right ih_left ih_right) \
                   node",
                "I04 Pudlak rule for shared pivots: at shared-variable resolution \
                 nodes, the interpolant is (pivot AND I_left) OR (NOT pivot AND I_right). \
                 Proof by induction on InterpNode using InterpNode.rec. \
                 A-input/B-input: base cases (PudlakWitness.a_input/b_input). \
                 A-pivot: disjunction of children (PudlakWitness.resolve_a_pivot). \
                 B-pivot: conjunction of children (PudlakWitness.resolve_b_pivot). \
                 Shared-pivot: Pudlak's guarded disjunction — if pivot is true, \
                 I reduces to I_left; if false, to I_right \
                 (PudlakWitness.resolve_shared). \
                 (Pudlak, 1997). Part of #3333.",
            ),
        );
    }
}

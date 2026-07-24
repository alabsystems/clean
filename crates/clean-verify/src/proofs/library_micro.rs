// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Micro-checker proof registration methods for ProofLibrary.
//!
//! Contains `add_micro_checker_proofs()` which populates the library
//! with micro-checker WHNF, soundness, and cross-validation proofs.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    /// Add micro-checker proofs
    pub(super) fn add_micro_checker_proofs(&mut self) {
        // Micro-checker WHNF correctness proofs

        // Lift zero is identity
        self.proofs.insert(
            "micro_lift_zero".to_string(),
            ProofTerm::new(
                "micro_lift_zero_id",
                "fun (e : MicroExpr) (c : Nat) => micro_lift_zero_id e c",
                "Lifting by zero is identity (micro-checker)",
            ),
        );

        // Instantiate BVar(0)
        self.proofs.insert(
            "micro_inst_bvar".to_string(),
            ProofTerm::new(
                "micro_instantiate_bvar_zero",
                "fun (v : MicroExpr) => micro_instantiate_bvar_zero v",
                "Instantiating BVar(0) gives the value (micro-checker)",
            ),
        );

        // WHNF idempotence (on weak-head-normal lambda forms; the unrestricted
        // form is false because micro_whnf is a single step — see the spec).
        self.proofs.insert(
            "micro_whnf_idem".to_string(),
            ProofTerm::new(
                "micro_whnf_idempotent",
                "fun (ty : MicroExpr) (body : MicroExpr) => micro_whnf_idempotent ty body",
                "WHNF is idempotent on weak-head-normal forms (micro-checker)",
            ),
        );

        // WHNF sort
        self.proofs.insert(
            "micro_whnf_sort".to_string(),
            ProofTerm::new(
                "micro_whnf_sort",
                "fun (l : MicroLevel) => micro_whnf_sort l",
                "Sorts are in WHNF (micro-checker)",
            ),
        );

        // WHNF lambda
        self.proofs.insert(
            "micro_whnf_lam".to_string(),
            ProofTerm::new(
                "micro_whnf_lam",
                "fun (ty : MicroExpr) (body : MicroExpr) => micro_whnf_lam ty body",
                "Lambdas are in WHNF (micro-checker)",
            ),
        );

        // WHNF pi
        self.proofs.insert(
            "micro_whnf_pi".to_string(),
            ProofTerm::new(
                "micro_whnf_pi",
                "fun (ty : MicroExpr) (body : MicroExpr) => micro_whnf_pi ty body",
                "Pis are in WHNF (micro-checker)",
            ),
        );

        // WHNF beta — single weak-head step: micro_whnf (app (lam) arg) =
        // micro_instantiate body arg (does NOT re-normalize the contractum).
        self.proofs.insert(
            "micro_whnf_beta".to_string(),
            ProofTerm::new(
                "micro_whnf_beta",
                "fun (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr) => micro_whnf_beta ty body arg",
                "WHNF performs one beta step (micro-checker)",
            ),
        );

        // def_eq reflexivity
        self.proofs.insert(
            "micro_def_eq_refl".to_string(),
            ProofTerm::new(
                "micro_def_eq_refl",
                "fun (e : MicroExpr) => micro_def_eq_refl e",
                "Definitional equality is reflexive (micro-checker)",
            ),
        );

        // def_eq symmetry
        self.proofs.insert(
            "micro_def_eq_symm".to_string(),
            ProofTerm::new(
                "micro_def_eq_symm",
                "fun (a : MicroExpr) (b : MicroExpr) => micro_def_eq_symm a b",
                "Definitional equality is symmetric (micro-checker)",
            ),
        );

        // Micro-checker soundness proofs

        // Verify soundness
        self.proofs.insert(
            "micro_verify_soundness".to_string(),
            ProofTerm::new(
                "micro_verify_sound",
                "fun (cert : MicroCert) (e : MicroExpr) (T : MicroExpr) (h : Eq MicroExpr (micro_verify cert e) T) => micro_verify_sound cert e T h",
                "If micro_verify succeeds, the typing is correct",
            ),
        );

        // Sort typing
        self.proofs.insert(
            "micro_sort_typing".to_string(),
            ProofTerm::new(
                "micro_sort_typing",
                "fun (l : MicroLevel) => micro_sort_typing l",
                "Sort l : Sort (succ l) (micro-checker)",
            ),
        );

        // Pi formation
        self.proofs.insert(
            "micro_pi_form".to_string(),
            ProofTerm::new(
                "micro_pi_formation",
                "fun (A : MicroExpr) (B : MicroExpr) (l1 : MicroLevel) (l2 : MicroLevel) (hA : micro_has_type A (MicroExpr.sort l1)) (hB : micro_has_type B (MicroExpr.sort l2)) => micro_pi_formation A B l1 l2 hA hB",
                "Pi formation rule (micro-checker)",
            ),
        );

        // Lambda typing
        self.proofs.insert(
            "micro_lam_type".to_string(),
            ProofTerm::new(
                "micro_lam_typing",
                "fun (A : MicroExpr) (b : MicroExpr) (B : MicroExpr) (hb : micro_has_type b B) => micro_lam_typing A b B hb",
                "Lambda typing rule (micro-checker)",
            ),
        );

        // Application typing
        self.proofs.insert(
            "micro_app_type".to_string(),
            ProofTerm::new(
                "micro_app_typing",
                "fun (f : MicroExpr) (a : MicroExpr) (A : MicroExpr) (B : MicroExpr) (hf : micro_has_type f (MicroExpr.pi A B)) (ha : micro_has_type a A) => micro_app_typing f a A B hf ha",
                "Application typing rule (micro-checker)",
            ),
        );

        // Type preservation
        self.proofs.insert(
            "micro_type_pres".to_string(),
            ProofTerm::new(
                "micro_type_preservation",
                "fun (e : MicroExpr) (T : MicroExpr) (e' : MicroExpr) (ht : micro_has_type e T) (heq : Eq Bool (micro_def_eq e e') Bool.true) => micro_type_preservation e T e' ht heq",
                "Type preservation (micro-checker)",
            ),
        );

        // Cross-validation proofs

        // Translation preserves typing
        self.proofs.insert(
            "trans_typing".to_string(),
            ProofTerm::new(
                "translation_preserves_typing",
                "fun (e : KExpr) (T : KExpr) (h : has_type e T) => translation_preserves_typing e T h",
                "Translation from kernel to micro preserves typing",
            ),
        );

        // Translation-preserves-def_eq proof REMOVED (Brick 3 of the micro-band
        // drain): it forwarded to `translation_preserves_def_eq`, which forwarded
        // to the FALSE `kernel_to_micro_def_eq` axiom. Both were refuted-and-deleted
        // (see micro_soundness.rs). The honest bridge is future capstone work.
    }
}

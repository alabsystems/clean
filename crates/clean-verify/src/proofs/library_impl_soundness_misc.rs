// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Miscellaneous implementation soundness proof terms for the kernel ProofLibrary.
//!
//! Covers DerivedProved definitions from:
//! - implementation_soundness.rs: KernelBinaryInputAdmissible, KernelInputAdmissible
//! - implementation_soundness_admissibility.rs: is_closed_at_* decomposition
//! - implementation_soundness_admissibility_wrappers.rs: kernel_input_admissible_*
//! - implementation_soundness_infer_refinement.rs: InferSoundAt, bvar_not_closed, etc.
//! - implementation_soundness_infer_refinement_dispatch.rs: infer_sound_at_bvar
//! - whnf_lemmas.rs: instantiate_at_pi_codomain_eq, instantiate_at_pi_self_codomain_eq
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_impl_soundness_misc_proofs(&mut self) {
        // === implementation_soundness.rs ===

        self.proofs.insert(
            "KernelBinaryInputAdmissible".to_string(),
            ProofTerm::new(
                "KernelBinaryInputAdmissible",
                "KernelBinaryInputAdmissible",
                "Binary input admissibility: both expressions are closed (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "KernelInputAdmissible".to_string(),
            ProofTerm::new(
                "KernelInputAdmissible",
                "fun (st : KernelState) (e : KExpr) => is_closed e",
                "Unary input admissibility: expression is closed (DerivedProved)",
            ),
        );

        // === implementation_soundness_admissibility.rs ===

        self.proofs.insert(
            "is_closed_at_app_fun".to_string(),
            ProofTerm::new(
                "is_closed_at_app_fun",
                "is_closed_at_app_fun",
                "If app(f, a) is closed at d then f is closed at d (DerivedProved via structural decomposition)",
            ),
        );

        self.proofs.insert(
            "is_closed_at_app_arg".to_string(),
            ProofTerm::new(
                "is_closed_at_app_arg",
                "is_closed_at_app_arg",
                "If app(f, a) is closed at d then a is closed at d (DerivedProved via structural decomposition)",
            ),
        );

        self.proofs.insert(
            "is_closed_at_lam_type".to_string(),
            ProofTerm::new(
                "is_closed_at_lam_type",
                "is_closed_at_lam_type",
                "If lam(A, b) is closed at d then A is closed at d (DerivedProved via structural decomposition)",
            ),
        );

        self.proofs.insert(
            "is_closed_at_pi_type".to_string(),
            ProofTerm::new(
                "is_closed_at_pi_type",
                "is_closed_at_pi_type",
                "If pi(A, B) is closed at d then A is closed at d (DerivedProved via structural decomposition)",
            ),
        );

        // === implementation_soundness_admissibility_wrappers.rs ===

        self.proofs.insert(
            "kernel_input_admissible_app_fun".to_string(),
            ProofTerm::new(
                "kernel_input_admissible_app_fun",
                "kernel_input_admissible_app_fun",
                "If app(f, a) is admissible then f is admissible (DerivedProved via is_closed_at_app_fun)",
            ),
        );

        self.proofs.insert(
            "kernel_input_admissible_app_arg".to_string(),
            ProofTerm::new(
                "kernel_input_admissible_app_arg",
                "kernel_input_admissible_app_arg",
                "If app(f, a) is admissible then a is admissible (DerivedProved via is_closed_at_app_arg)",
            ),
        );

        self.proofs.insert(
            "kernel_input_admissible_lam_type".to_string(),
            ProofTerm::new(
                "kernel_input_admissible_lam_type",
                "kernel_input_admissible_lam_type",
                "If lam(A, b) is admissible then A is admissible (DerivedProved via is_closed_at_lam_type)",
            ),
        );

        self.proofs.insert(
            "kernel_input_admissible_pi_type".to_string(),
            ProofTerm::new(
                "kernel_input_admissible_pi_type",
                "kernel_input_admissible_pi_type",
                "If pi(A, B) is admissible then A is admissible (DerivedProved via is_closed_at_pi_type)",
            ),
        );

        // === implementation_soundness_infer_refinement.rs ===

        self.proofs.insert(
            "InferSoundAt".to_string(),
            ProofTerm::new(
                "InferSoundAt",
                "InferSoundAt",
                "Per-constructor infer soundness predicate (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "bvar_not_closed".to_string(),
            ProofTerm::new(
                "bvar_not_closed",
                "bvar_not_closed",
                "BVar n is not closed (DerivedProved via is_closed_at inversion)",
            ),
        );

        self.proofs.insert(
            "is_closed_at_bvar_inv".to_string(),
            ProofTerm::new(
                "is_closed_at_bvar_inv",
                "is_closed_at_bvar_inv",
                "is_closed_at (bvar n) 0 is empty (DerivedProved via structural inversion)",
            ),
        );

        self.proofs.insert(
            "not_lt_zero".to_string(),
            ProofTerm::new(
                "not_lt_zero",
                "not_lt_zero",
                "No natural number is less than zero (DerivedProved via Nat.rec)",
            ),
        );

        self.proofs.insert(
            "not_lt_zero_goal".to_string(),
            ProofTerm::new(
                "not_lt_zero_goal",
                "not_lt_zero_goal",
                "Motive alias for not_lt_zero induction (DerivedProved)",
            ),
        );

        // === implementation_soundness_infer_refinement_dispatch.rs ===

        self.proofs.insert(
            "infer_sound_at_bvar".to_string(),
            ProofTerm::new(
                "infer_sound_at_bvar",
                "infer_sound_at_bvar",
                "Infer soundness at bvar: vacuously true because bvar is never closed (DerivedProved via bvar_not_closed)",
            ),
        );

        // === whnf_lemmas.rs: Pi codomain equality helpers ===

        self.proofs.insert(
            "instantiate_at_pi_codomain_eq".to_string(),
            ProofTerm::new(
                "instantiate_at_pi_codomain_eq",
                "instantiate_at_pi_codomain_eq",
                "instantiate_at (pi A B) val depth codomain extraction (DerivedProved via instantiate_at_pi + Eq.cong)",
            ),
        );

        self.proofs.insert(
            "instantiate_at_pi_self_codomain_eq".to_string(),
            ProofTerm::new(
                "instantiate_at_pi_self_codomain_eq",
                "instantiate_at_pi_self_codomain_eq",
                "Self-codomain extraction for instantiate_at on Pi (DerivedProved)",
            ),
        );
    }
}

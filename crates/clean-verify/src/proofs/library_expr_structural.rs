// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression structural proof terms for the kernel ProofLibrary.
//!
//! Covers DerivedProved definitions from:
//! - expr_model_discrimination.rs: App discrimination (kexpr_not_app, sort/lam/pi_ne_app,
//!   app_fst, app_snd, app_inj_fst, app_inj_snd)
//! - expr_model_discrimination_lam_pi.rs: Lam discrimination
//! - expr_model_discrimination_pi.rs: Pi discrimination
//! - pi_injectivity_confluence.rs: pi_def_eq_eq
//! - pi_injectivity_def_eq.rs: pi_injectivity_def_eq_dom, pi_injectivity_def_eq_cod
//! - typing_def_eq.rs: is_def_eq
//! - typing_def_eq_typed.rs: typed_def_eq_to_def_eq, typing_is_def_eq
//! - typing_universe_levels.rs: imax_nat
//! - type_preservation_generation.rs: typing_sort_gen, typing_pi_gen, typing_lam_gen
//! - type_preservation_generation_app.rs: typing_app_gen
//! - type_preservation_cases_congruence.rs: pi_type_preservation, pi_type_preservation_inv
//! - micro_checker.rs: micro_instantiate_sort
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_expr_structural_proofs(&mut self) {
        // === App discrimination (expr_model_discrimination.rs) ===

        self.proofs.insert(
            "kexpr_not_app".to_string(),
            ProofTerm::new(
                "kexpr_not_app",
                "kexpr_not_app",
                "Large-elimination discriminator: non-App constructors -> Nat, App -> Empty (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "sort_ne_app".to_string(),
            ProofTerm::new(
                "sort_ne_app",
                "sort_ne_app",
                "Sort /= App discrimination via Eq.substType + discriminator + Empty.rec (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lam_ne_app".to_string(),
            ProofTerm::new(
                "lam_ne_app",
                "lam_ne_app",
                "Lam /= App discrimination via Eq.substType + discriminator + Empty.rec (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_ne_app".to_string(),
            ProofTerm::new(
                "pi_ne_app",
                "pi_ne_app",
                "Pi /= App discrimination via Eq.substType + discriminator + Empty.rec (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "app_fst".to_string(),
            ProofTerm::new(
                "app_fst",
                "app_fst",
                "Extract function from App via match (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "app_snd".to_string(),
            ProofTerm::new(
                "app_snd",
                "app_snd",
                "Extract argument from App via match (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "app_inj_fst".to_string(),
            ProofTerm::new(
                "app_inj_fst",
                "app_inj_fst",
                "App injectivity (fst): App f1 a1 = App f2 a2 -> f1 = f2 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "app_inj_snd".to_string(),
            ProofTerm::new(
                "app_inj_snd",
                "app_inj_snd",
                "App injectivity (snd): App f1 a1 = App f2 a2 -> a1 = a2 (DerivedProved)",
            ),
        );

        // === Lam discrimination (expr_model_discrimination_lam_pi.rs) ===

        self.proofs.insert(
            "kexpr_not_lam".to_string(),
            ProofTerm::new(
                "kexpr_not_lam",
                "kexpr_not_lam",
                "Large-elimination discriminator: non-Lam -> Nat, Lam -> Empty (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "sort_ne_lam".to_string(),
            ProofTerm::new(
                "sort_ne_lam",
                "sort_ne_lam",
                "Sort /= Lam discrimination (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "app_ne_lam".to_string(),
            ProofTerm::new(
                "app_ne_lam",
                "app_ne_lam",
                "App /= Lam discrimination (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_ne_lam".to_string(),
            ProofTerm::new(
                "pi_ne_lam",
                "pi_ne_lam",
                "Pi /= Lam discrimination (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lam_fst".to_string(),
            ProofTerm::new(
                "lam_fst",
                "lam_fst",
                "Extract domain from Lam via match (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lam_snd".to_string(),
            ProofTerm::new(
                "lam_snd",
                "lam_snd",
                "Extract body from Lam via match (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lam_inj_fst".to_string(),
            ProofTerm::new(
                "lam_inj_fst",
                "lam_inj_fst",
                "Lam injectivity (fst): Lam A1 b1 = Lam A2 b2 -> A1 = A2 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lam_inj_snd".to_string(),
            ProofTerm::new(
                "lam_inj_snd",
                "lam_inj_snd",
                "Lam injectivity (snd): Lam A1 b1 = Lam A2 b2 -> b1 = b2 (DerivedProved)",
            ),
        );

        // === Pi discrimination (expr_model_discrimination_pi.rs) ===

        self.proofs.insert(
            "kexpr_not_pi".to_string(),
            ProofTerm::new(
                "kexpr_not_pi",
                "kexpr_not_pi",
                "Large-elimination discriminator: non-Pi -> Nat, Pi -> Empty (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "sort_ne_pi".to_string(),
            ProofTerm::new(
                "sort_ne_pi",
                "sort_ne_pi",
                "Sort /= Pi discrimination (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "app_ne_pi".to_string(),
            ProofTerm::new(
                "app_ne_pi",
                "app_ne_pi",
                "App /= Pi discrimination (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "lam_ne_pi".to_string(),
            ProofTerm::new(
                "lam_ne_pi",
                "lam_ne_pi",
                "Lam /= Pi discrimination (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_fst".to_string(),
            ProofTerm::new(
                "pi_fst",
                "pi_fst",
                "Extract domain from Pi via match (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_snd".to_string(),
            ProofTerm::new(
                "pi_snd",
                "pi_snd",
                "Extract codomain from Pi via match (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_inj_fst".to_string(),
            ProofTerm::new(
                "pi_inj_fst",
                "pi_inj_fst",
                "Pi injectivity (fst): Pi A1 B1 = Pi A2 B2 -> A1 = A2 (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_inj_snd".to_string(),
            ProofTerm::new(
                "pi_inj_snd",
                "pi_inj_snd",
                "Pi injectivity (snd): Pi A1 B1 = Pi A2 B2 -> B1 = B2 (DerivedProved)",
            ),
        );

        // === Pi DefEq injectivity (pi_injectivity_*.rs) ===
        // pi_def_eq_eq library proof removed: the spec decl is deleted (#2859,
        // false Eq shim backed by the retired church_rosser_whnf axiom).

        self.proofs.insert(
            "pi_injectivity_def_eq_dom".to_string(),
            ProofTerm::new(
                "pi_injectivity_def_eq_dom",
                "pi_injectivity_def_eq_dom",
                "Pi DefEq injectivity (domain): DefEq (Pi A B) (Pi A' B') -> DefEq A A' (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "pi_injectivity_def_eq_cod".to_string(),
            ProofTerm::new(
                "pi_injectivity_def_eq_cod",
                "pi_injectivity_def_eq_cod",
                "Pi DefEq injectivity (codomain): DefEq (Pi A B) (Pi A' B') -> DefEq B B' (DerivedProved)",
            ),
        );

        // === Typing/DefEq bridge (typing_def_eq*.rs) ===

        self.proofs.insert(
            "is_def_eq".to_string(),
            ProofTerm::new(
                "is_def_eq",
                "is_def_eq",
                "Prop-level definitional equality wrapper (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "typed_def_eq_to_def_eq".to_string(),
            ProofTerm::new(
                "typed_def_eq_to_def_eq",
                "typed_def_eq_to_def_eq",
                "Extract DefEq from TypedDefEq (DerivedProved)",
            ),
        );

        self.proofs.insert(
            "typing_is_def_eq".to_string(),
            ProofTerm::new(
                "typing_is_def_eq",
                "typing_is_def_eq",
                "Typing-aware is_def_eq bridge (DerivedProved)",
            ),
        );

        // === Universe levels (typing_universe_levels.rs) ===

        self.proofs.insert(
            "imax_nat".to_string(),
            ProofTerm::new(
                "imax_nat",
                "imax_nat",
                "imax on Nat universe levels (DerivedProved)",
            ),
        );

        // === Type preservation generation lemmas ===

        self.proofs.insert(
            "typing_sort_gen".to_string(),
            ProofTerm::new(
                "typing_sort_gen",
                "typing_sort_gen",
                "Typing generation: has_type (sort n) T -> T = sort (succ n) (DerivedProved via Typing.rec)",
            ),
        );

        self.proofs.insert(
            "typing_pi_gen".to_string(),
            ProofTerm::new(
                "typing_pi_gen",
                "typing_pi_gen",
                "Typing generation: has_type (pi A B) T -> exists levels (DerivedProved via Typing.rec)",
            ),
        );

        self.proofs.insert(
            "typing_lam_gen".to_string(),
            ProofTerm::new(
                "typing_lam_gen",
                "typing_lam_gen",
                "Typing generation: has_type (lam A b) T -> exists Pi type (DerivedProved via Typing.rec)",
            ),
        );

        self.proofs.insert(
            "typing_app_gen".to_string(),
            ProofTerm::new(
                "typing_app_gen",
                "typing_app_gen",
                "Typing generation: has_type (app f a) T -> exists Pi and substitution (DerivedProved via Typing.rec)",
            ),
        );

        // === Pi type preservation (type_preservation_cases_congruence.rs) ===

        self.proofs.insert(
            "pi_type_preservation".to_string(),
            ProofTerm::new(
                "pi_type_preservation",
                "pi_type_preservation",
                "Pi type preservation: congruence preserves typing (DerivedProved via Typing.rec)",
            ),
        );

        self.proofs.insert(
            "pi_type_preservation_inv".to_string(),
            ProofTerm::new(
                "pi_type_preservation_inv",
                "pi_type_preservation_inv",
                "Pi type preservation (reverse): congruence backwards preserves typing (DerivedProved via Typing.rec)",
            ),
        );

        // === Micro-checker (micro_checker.rs) ===

        self.proofs.insert(
            "micro_instantiate_sort".to_string(),
            ProofTerm::new(
                "micro_instantiate_sort",
                "micro_instantiate_sort",
                "Micro-checker instantiate on sort is identity (DerivedProved)",
            ),
        );
    }
}

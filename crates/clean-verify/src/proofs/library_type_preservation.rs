// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-preservation proof registrations for `ProofLibrary`.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    /// Add type-preservation proof terms and chain helpers.
    pub(super) fn add_type_preservation_proofs(&mut self) {
        self.proofs.insert(
            "TypePreservation".to_string(),
            ProofTerm::new(
                "TypePreservation",
                "fun (e : KExpr) (T : KExpr) (e' : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (ht : has_type e T) (heq : typing_is_def_eq e e') => def_eq_preserves_typing e e' T wd wr ht heq",
                "Type preservation: typing is preserved across typed definitional equality.",
            ),
        );

        self.proofs.insert(
            "type_preservation_helper".to_string(),
            ProofTerm::new(
                "def_eq_preserves_typing",
                "fun (hf : RedEnvFaithful the_red_env) (e : KExpr) (e' : KExpr) (T : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (h_type : has_type e T) (h_eq : typing_is_def_eq e e') => def_eq_preserves_typing hf e e' T wd wr h_type h_eq",
                "Primary helper theorem for the typed type-preservation surface.",
            ),
        );

        self.proofs.insert(
            "beta_lam_dom_sort".to_string(),
            ProofTerm::new(
                "lam_typing_dom_sort",
                "fun (A_dom : KExpr) (body : KExpr) (T : KExpr) (R : Type) (hlam : Typing (KExpr.lam A_dom body) T) (k : forall (u : Level), Typing A_dom (KExpr.sort u) -> R) => lam_typing_dom_sort A_dom body T R hlam k",
                "Beta helper: recover a sort witness for the lambda domain from a lambda typing derivation.",
            ),
        );

        self.proofs.insert(
            "beta_lam_body_subst".to_string(),
            ProofTerm::new(
                "lam_typing_body_subst",
                "fun (hf : RedEnvFaithful the_red_env) (A_dom : KExpr) (body : KExpr) (A0 : KExpr) (B0 : KExpr) (arg : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (hlam : Typing (KExpr.lam A_dom body) (KExpr.pi A0 B0)) (harg : Typing arg A0) => lam_typing_body_subst hf A_dom body A0 B0 arg wd wr hlam harg",
                "Beta helper: invert lambda typing and discharge the body substitution step.",
            ),
        );

        self.proofs.insert(
            "beta_type_preservation".to_string(),
            ProofTerm::new(
                "beta_preservation",
                "fun (hf : RedEnvFaithful the_red_env) (A : KExpr) (b : KExpr) (a : KExpr) (T : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (h : has_type (KExpr.app (KExpr.lam A b) a) T) => beta_preservation hf A b a T wd wr h",
                "Beta preservation: (λA.b) a : T implies b[a/x] : T.",
            ),
        );

        self.proofs.insert(
            "beta_type_expansion".to_string(),
            ProofTerm::new(
                "beta_expansion",
                "fun (hf : RedEnvFaithful the_red_env) (A : KExpr) (body : KExpr) (arg : KExpr) (B : KExpr) (T : KExpr) (u : Level) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (hA : has_type A (KExpr.sort u)) (hbody : has_type body B) (harg : has_type arg A) (hinst : has_type (instantiate body arg) T) => beta_expansion hf A body arg B T u wd wr hA hbody harg hinst",
                "Typed beta expansion: reconstruct the redex typing from the substituted body typing.",
            ),
        );

        self.proofs.insert(
            "subst_typing".to_string(),
            ProofTerm::new(
                "substitution_typing",
                "fun (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (u : Level) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (hA : has_type A (KExpr.sort u)) (hb : has_type b B) (ha : has_type a A) => substitution_typing A B b a u wd wr hA hb ha",
                "Substitution preserves typing.",
            ),
        );

        self.proofs.insert(
            "type_conv".to_string(),
            ProofTerm::new(
                "type_conversion",
                "fun (e : KExpr) (T1 : KExpr) (T2 : KExpr) (h1 : has_type e T1) (h2 : typing_is_def_eq T1 T2) => type_conversion e T1 T2 h1 h2",
                "Type conversion: e : T1 and T1 ≡ T2 implies e : T2.",
            ),
        );

        self.proofs.insert(
            "sort_universe_consistency".to_string(),
            ProofTerm::new(
                "sort_universe_consistency",
                "fun (n : Level) (m : Level) (h : Eq KExpr (KExpr.sort n) (KExpr.sort m)) => sort_universe_consistency n m h",
                "Sort equality preserves the underlying universe indices.",
            ),
        );

        self.proofs.insert(
            "app_cong".to_string(),
            ProofTerm::new(
                "def_eq_app_cong",
                "fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (hf : DefEq f f') (ha : DefEq a a') => def_eq_app_cong f f' a a' hf ha",
                "Application congruence via DefEq.app_cong.",
            ),
        );

        self.proofs.insert(
            "lam_cong".to_string(),
            ProofTerm::new(
                "def_eq_lam_cong",
                "fun (A : KExpr) (b : KExpr) (b' : KExpr) (h : DefEq b b') => def_eq_lam_cong A b b' h",
                "Lambda congruence via DefEq.lam_cong.",
            ),
        );

        self.proofs.insert(
            "pi_cong".to_string(),
            ProofTerm::new(
                "def_eq_pi_cong",
                "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (hA : DefEq A A') (hB : DefEq B B') => def_eq_pi_cong A A' B B' hA hB",
                "Pi congruence via DefEq.pi_cong.",
            ),
        );
    }
}

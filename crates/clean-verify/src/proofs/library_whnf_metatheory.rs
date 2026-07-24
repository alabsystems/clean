// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WHNF metatheory proof terms for the kernel ProofLibrary.
//!
//! Covers DerivedProved definitions from:
//! - implementation_soundness_whnf_decomposition.rs: motive aliases, beta/delta sound
//!   wrappers, whnf_step/whnf_to bridges, target-is-WHNF extraction
//! - whnf_lemmas.rs: instantiate_at structural lemmas, value_is_whnf, instantiate_const
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_whnf_metatheory_proofs(&mut self) {
        // === implementation_soundness_whnf_decomposition.rs ===

        // Semireducible motive alias: beta_reduces e e' -> Type := DefEq e e'
        self.proofs.insert(
            "beta_reduces_def_eq_goal".to_string(),
            ProofTerm::new(
                "beta_reduces_def_eq_goal",
                "fun (e : KExpr) (e' : KExpr) (_h : beta_reduces e e') => DefEq e e'",
                "Semireducible motive alias for beta_reduces-to-DefEq bridge (DerivedProved)",
            ),
        );

        // whnf_step beta-case wrapper: delegates to beta_reduces_preserves_def_eq
        self.proofs.insert(
            "whnf_step_beta_sound".to_string(),
            ProofTerm::new(
                "whnf_step_beta_sound",
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : beta_reduces e e') => ",
                    "beta_reduces_preserves_def_eq e e' h"
                ),
                "Named whnf_step.rec beta-case wrapper (DerivedProved via delegation to beta_reduces_preserves_def_eq)",
            ),
        );

        // Semireducible motive alias: whnf_step e e' -> Type := DefEq e e'
        self.proofs.insert(
            "whnf_step_def_eq_goal".to_string(),
            ProofTerm::new(
                "whnf_step_def_eq_goal",
                "fun (e : KExpr) (e' : KExpr) (_h : whnf_step e e') => DefEq e e'",
                "Semireducible motive alias for whnf_step-to-DefEq bridge (DerivedProved)",
            ),
        );

        // Single-step WHNF bridge: whnf_step e e' -> DefEq e e'
        // via whnf_step.rec with beta and delta case wrappers
        self.proofs.insert(
            "whnf_step_preserves_def_eq".to_string(),
            ProofTerm::new(
                "whnf_step_preserves_def_eq",
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : whnf_step e e') => ",
                    "whnf_step.rec e e' ",
                    "(whnf_step_def_eq_goal e e') ",
                    "(whnf_step_beta_sound e e') ",
                    "(whnf_step_delta_sound e e') ",
                    "h"
                ),
                "Single-step WHNF bridge via whnf_step.rec (DerivedProved via beta + delta sound wrappers)",
            ),
        );

        // Semireducible motive alias: whnf_to e v -> Type := DefEq e v
        self.proofs.insert(
            "whnf_to_def_eq_goal".to_string(),
            ProofTerm::new(
                "whnf_to_def_eq_goal",
                "fun (e : KExpr) (e' : KExpr) (_h : whnf_to e e') => DefEq e e'",
                "Semireducible motive alias for whnf_to-to-DefEq bridge (DerivedProved)",
            ),
        );

        // Semireducible motive alias for whnf_to target-is-WHNF induction
        self.proofs.insert(
            "whnf_to_is_whnf_goal".to_string(),
            ProofTerm::new(
                "whnf_to_is_whnf_goal",
                "fun (_e : KExpr) (v : KExpr) (_h : whnf_to _e v) => is_whnf v",
                "Semireducible motive alias for whnf_to target-is-WHNF induction (DerivedProved)",
            ),
        );

        // whnf_to target is WHNF: whnf_to e v -> is_whnf v
        // via whnf_to.rec: refl case has is_whnf directly, step case passes IH
        self.proofs.insert(
            "whnf_to_target_is_whnf".to_string(),
            ProofTerm::new(
                "whnf_to_target_is_whnf",
                concat!(
                    "fun (e : KExpr) (v : KExpr) (h : whnf_to e v) => ",
                    "whnf_to.rec ",
                    "whnf_to_is_whnf_goal ",
                    "(fun (_e0 : KExpr) (hwhnf : is_whnf _e0) => hwhnf) ",
                    "(fun (_e0 : KExpr) (_e1 : KExpr) (_v : KExpr) ",
                    "(_hstep : whnf_step _e0 _e1) ",
                    "(_hrest : whnf_to _e1 _v) ",
                    "(ih : whnf_to_is_whnf_goal _e1 _v _hrest) => ih) ",
                    "e v h"
                ),
                "WHNF target extraction via whnf_to.rec induction (DerivedProved)",
            ),
        );

        // === whnf_lemmas.rs: instantiate_at structural lemmas ===

        // instantiate_at (sort n) val depth = sort n
        self.proofs.insert(
            "instantiate_at_sort".to_string(),
            ProofTerm::new(
                "instantiate_at_sort",
                "fun (n : Level) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.sort n)",
                "instantiate_at distributes trivially over sort (DerivedProved via Eq.refl)",
            ),
        );

        // instantiate_at (const n us) val depth = const n us
        self.proofs.insert(
            "instantiate_at_const".to_string(),
            ProofTerm::new(
                "instantiate_at_const",
                "fun (n : Name) (us : ListType Level) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.const n us)",
                "instantiate_at distributes trivially over const (DerivedProved via Eq.refl)",
            ),
        );

        // instantiate_at (app f a) val depth = app (instantiate_at f val depth) (instantiate_at a val depth)
        self.proofs.insert(
            "instantiate_at_app".to_string(),
            ProofTerm::new(
                "instantiate_at_app",
                "fun (f : KExpr) (a : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.app (instantiate_at f val depth) (instantiate_at a val depth))",
                "instantiate_at distributes over app (DerivedProved via Eq.refl + structural registration)",
            ),
        );

        // instantiate_at (lam ty b) val depth = lam (instantiate_at ty val depth) (instantiate_at b val (succ depth))
        self.proofs.insert(
            "instantiate_at_lam".to_string(),
            ProofTerm::new(
                "instantiate_at_lam",
                "fun (ty : KExpr) (b : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.lam (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth)))",
                "instantiate_at distributes over lam with depth increment (DerivedProved via Eq.refl + structural registration)",
            ),
        );

        // instantiate_at (pi ty b) val depth = pi (instantiate_at ty val depth) (instantiate_at b val (succ depth))
        self.proofs.insert(
            "instantiate_at_pi".to_string(),
            ProofTerm::new(
                "instantiate_at_pi",
                "fun (ty : KExpr) (b : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.pi (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth)))",
                "instantiate_at distributes over pi with depth increment (DerivedProved via Eq.refl + structural registration)",
            ),
        );

        // instantiate_const: instantiate (const n us) val = const n us
        self.proofs.insert(
            "instantiate_const".to_string(),
            ProofTerm::new(
                "instantiate_const",
                "fun (n : Name) (us : ListType Level) (val : KExpr) => Eq.refl KExpr (KExpr.const n us)",
                "instantiate on const is identity (DerivedProved via Eq.refl)",
            ),
        );

        // value_is_whnf: is_value e -> is_whnf e via is_value.rec
        self.proofs.insert(
            "value_is_whnf".to_string(),
            ProofTerm::new(
                "value_is_whnf",
                concat!(
                    "fun (e : KExpr) (h : is_value e) => ",
                    "is_value.rec ",
                    "(fun (e0 : KExpr) (_ : is_value e0) => is_whnf e0) ",
                    "(fun (n : Level) => is_whnf.sort n) ",
                    "(fun (ty : KExpr) (body : KExpr) => is_whnf.lam ty body) ",
                    "(fun (ty : KExpr) (body : KExpr) => is_whnf.pi ty body) ",
                    "e h"
                ),
                "Legacy values are bounded WHNFs (DerivedProved via is_value.rec into is_whnf constructors)",
            ),
        );
    }
}

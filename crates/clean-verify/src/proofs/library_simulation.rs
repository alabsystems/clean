// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Forward simulation and implementation soundness proof registrations (#461).
//!
//! Split from `library.rs` for file-size compliance. Contains:
//! - `add_forward_simulation_proofs()`: WHNF bridge proofs + forward simulation theorems + DefEq transport
//! - `add_implementation_soundness_proofs()`: KernelStateMatchesSpec bridge proofs

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    /// Add WHNF bridge and forward simulation proofs (#461)
    ///
    /// These proofs witness the constructive bridges from spec reduction
    /// predicates (beta_reduces, whnf_to) to DefEq, and the forward
    /// simulation theorems connecting kernel functions to spec judgments.
    pub(super) fn add_forward_simulation_proofs(&mut self) {
        // ---- WHNF bridge proofs (fully constructive) ----

        // beta_reduces → DefEq bridge via beta_reduces.rec
        self.proofs.insert(
            "beta_reduces_preserves_def_eq".to_string(),
            ProofTerm::new(
                "beta_reduces_preserves_def_eq",
                "beta_reduces_preserves_def_eq",
                "Single-step beta/compatibility bridge from beta_reduces to DefEq (DerivedProved via beta_reduces.rec)",
            ),
        );

        // whnf_to → DefEq closure bridge via whnf_to.rec
        self.proofs.insert(
            "whnf_to_preserves_def_eq".to_string(),
            ProofTerm::new(
                "whnf_to_preserves_def_eq",
                "whnf_to_preserves_def_eq",
                "Spec-closure bridge from whnf_to to DefEq (DerivedProved via whnf_to.rec + beta_reduces bridge)",
            ),
        );

        // ---- Forward simulation theorems ----

        // KernelWhnfSound: kernel whnf → spec is_def_eq
        self.proofs.insert(
            "KernelWhnfSound".to_string(),
            ProofTerm::new(
                "KernelWhnfSound",
                "fun (st : KernelState) (e : KExpr) (e' : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') => kernel_whnf_returns_def_eq st e e' henv hctx hin haccept",
                "Forward simulation for whnf: kernel WHNF output is spec-definitionally-equal to input",
            ),
        );

        // KernelInferSound: kernel infer → spec has_type
        self.proofs.insert(
            "KernelInferSound".to_string(),
            ProofTerm::new(
                "KernelInferSound",
                "fun (st : KernelState) (e : KExpr) (T : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelInferAccepts st e T) => kernel_infer_returns_well_typed st e T henv hctx hin haccept",
                "Forward simulation for infer_type: kernel inference result is spec-well-typed",
            ),
        );

        // KernelDefEqSound: kernel def_eq → spec is_def_eq
        self.proofs.insert(
            "KernelDefEqSound".to_string(),
            ProofTerm::new(
                "KernelDefEqSound",
                "fun (st : KernelState) (a : KExpr) (b : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelBinaryInputAdmissible st a b) (haccept : KernelDefEqAccepts st a b) => kernel_def_eq_reflects_spec st a b henv hctx hin haccept",
                "Forward simulation for is_def_eq: kernel definitional equality reflects spec DefEq",
            ),
        );

        // ---- DefEq transport lemmas ----

        // def_eq_eq_left: transport DefEq along propositional Eq on left
        self.proofs.insert(
            "def_eq_eq_left".to_string(),
            ProofTerm::new(
                "def_eq_eq_left",
                "fun (a : KExpr) (a' : KExpr) (b : KExpr) (eq : Eq KExpr a a') (h : DefEq a' b) => Eq.substType KExpr (fun (x : KExpr) => DefEq x b) a' a (Eq.symm KExpr a a' eq) h",
                "Transport DefEq left: Eq a a' -> DefEq a' b -> DefEq a b",
            ),
        );

        // def_eq_eq_right: transport DefEq along propositional Eq on right
        self.proofs.insert(
            "def_eq_eq_right".to_string(),
            ProofTerm::new(
                "def_eq_eq_right",
                "fun (a : KExpr) (b' : KExpr) (b : KExpr) (h : DefEq a b') (eq : Eq KExpr b' b) => Eq.substType KExpr (fun (x : KExpr) => DefEq a x) b' b eq h",
                "Transport DefEq right: DefEq a b' -> Eq b' b -> DefEq a b",
            ),
        );
    }

    /// Add implementation soundness bridge proofs (#461)
    ///
    /// These proofs witness that the KernelStateMatchesSpec bridge axioms
    /// are constructively derivable from the AndType conjunction that underlies
    /// the summary alias. They cannot be registered as valued definitions in
    /// the spec because KernelStateMatchesSpec is Opaque, but the proof
    /// dependency audit captures them here.
    pub(super) fn add_implementation_soundness_proofs(&mut self) {
        // KernelStateMatchesSpec.mk via AndType.intro
        self.proofs.insert(
            "impl_state_matches_spec_mk".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec.mk",
                "fun (st : KernelState) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) => AndType.intro (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) henv hctx",
                "Summary builder is constructive via AndType.intro (KernelStateMatchesSpec unfolds to the split-state conjunction).",
            ),
        );

        // KernelStateMatchesSpec.envValid via AndType.left
        self.proofs.insert(
            "impl_state_matches_spec_env_valid".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec.envValid",
                "fun (st : KernelState) (h : KernelStateMatchesSpec st) => AndType.left (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) h",
                "Environment-validity eliminator is constructive via AndType.left.",
            ),
        );

        // KernelStateMatchesSpec.ctxWellFormed via AndType.right
        self.proofs.insert(
            "impl_state_matches_spec_ctx_well_formed".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec.ctxWellFormed",
                "fun (st : KernelState) (h : KernelStateMatchesSpec st) => AndType.right (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) h",
                "Local-context well-formedness eliminator is constructive via AndType.right.",
            ),
        );
    }
}

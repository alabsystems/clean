// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implementation soundness decomposition proof terms for the kernel ProofLibrary.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_impl_soundness_decomp_proofs(&mut self) {
        // =========================================================
        // WHNF decomposition proof terms
        // =========================================================

        // whnf_step delta-case wrapper
        self.proofs.insert(
            "whnf_step_delta_sound".to_string(),
            ProofTerm::new(
                "whnf_step_delta_sound",
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : delta_reduces e e') => ",
                    "DefEq.delta e e' h"
                ),
                "Named whnf_step.rec delta-case wrapper: delta_reduces yields DefEq.delta directly",
            ),
        );

        // kernel_whnf_returns_def_eq: forward simulation for whnf
        self.proofs.insert(
            "kernel_whnf_returns_def_eq".to_string(),
            ProofTerm::new(
                "kernel_whnf_returns_def_eq",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (e' : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hin : KernelInputAdmissible st e) ",
                    "(haccept : KernelWhnfAccepts st e e') => ",
                    "whnf_to_preserves_def_eq e e' ",
                    "(kernel_whnf_reduces_to_spec_whnf st e e' henv hctx hin haccept)"
                ),
                "Forward simulation for whnf: derived from spec whnf trace witness plus constructive whnf_to-to-DefEq closure bridge",
            ),
        );

        // =========================================================
        // check_type decomposition proof terms
        // =========================================================

        // kernel_check_infer_step / kernel_check_defeq_step are RETIRED
        // (KernelInferResult un-Skolemization): their types projected the infer /
        // defeq half AT the Skolem KernelInferResult st e, which no longer exists
        // (KernelCheckAccepts.mk binds the inferred type R existentially, shared by
        // binding). A standalone projection existentializes R independently and
        // loses that sharing — so they are retired, and the two halves are recovered
        // together inside kernel_check_returns_well_typed_from_infer / tc_check_completeness
        // by eliminating KernelCheckAccepts.rec (binding R once).

        // kernel_check_returns_well_typed_from_infer: local bridge parameterized by infer-soundness
        self.proofs.insert(
            "kernel_check_returns_well_typed_from_infer".to_string(),
            ProofTerm::new(
                "kernel_check_returns_well_typed_from_infer",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer_sound : forall (T' : KExpr), KernelInferAccepts st e T' -> has_type e T') ",
                    "(hcheck : KernelCheckAccepts st e T) => ",
                    "KernelCheckAccepts.rec st e T ",
                    "(fun (_c : KernelCheckAccepts st e T) => has_type e T) ",
                    "(fun (R : KExpr) ",
                    "(hpair : ProdType (KernelInferAccepts st e R) (KernelDefEqAccepts st R T)) ",
                    "(hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st e -> KernelBinaryInputAdmissible st R T) => ",
                    "raw_type_conversion e R T ",
                    "(hinfer_sound R ",
                    "(ProdType.fst (KernelInferAccepts st e R) (KernelDefEqAccepts st R T) hpair)) ",
                    "(kernel_def_eq_reflects_spec st R T ",
                    "henv hctx ",
                    "(hguard henv hctx hadm) ",
                    "(ProdType.snd (KernelInferAccepts st e R) (KernelDefEqAccepts st R T) hpair))) ",
                    "hcheck"
                ),
                "Local check_type soundness bridge: eliminate KernelCheckAccepts.rec (bind the inferred type R), then raw_type_conversion over the infer-soundness premise and kernel_def_eq_reflects_spec",
            ),
        );

        // kernel_check_returns_well_typed: global check_type soundness
        self.proofs.insert(
            "kernel_check_returns_well_typed".to_string(),
            ProofTerm::new(
                "kernel_check_returns_well_typed",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hcheck : KernelCheckAccepts st e T) => ",
                    "kernel_check_returns_well_typed_from_infer st e T ",
                    "henv hctx hadm ",
                    "(fun (T' : KExpr) (hinfer : KernelInferAccepts st e T') => ",
                    "kernel_infer_returns_well_typed st e T' henv hctx hadm hinfer) ",
                    "hcheck"
                ),
                "Forward simulation for check_type: derived from decomposition via infer + defeq",
            ),
        );

        // =========================================================
        // is_def_eq reflection proof terms
        // =========================================================

        // def_eq_joinable_reflects: eliminate the DefEqJoinable packaged existential
        // (which retires the KernelDefEqNormalLeft/Right skolems) to DefEq a b. The
        // minor binds the ctor's non-parameter fields (nl, nr, h1, h2, h3); a/b are
        // the recursor's leading parameters. a ≡ nl ≡ nr ≡ b by DefEq.trans/symm.
        self.proofs.insert(
            "def_eq_joinable_reflects".to_string(),
            ProofTerm::new(
                "def_eq_joinable_reflects",
                concat!(
                    "fun (a : KExpr) (b : KExpr) (h : DefEqJoinable a b) => ",
                    "DefEqJoinable.rec a b ",
                    "(fun (_h : DefEqJoinable a b) => DefEq a b) ",
                    "(fun (nl : KExpr) (nr : KExpr) ",
                    "(h1 : DefEq a nl) (h2 : DefEq b nr) (h3 : DefEq nl nr) => ",
                    "DefEq.trans a nl b h1 ",
                    "(DefEq.trans nl nr b h3 (DefEq.symm b nr h2))) ",
                    "h"
                ),
                "Eliminate DefEqJoinable to DefEq via DefEqJoinable.rec: a ≡ nl ≡ nr ≡ b by DefEq.trans/symm. Skolem-free.",
            ),
        );

        // kernel_def_eq_reflects_spec: forward simulation for is_def_eq. Eliminate the
        // KernelDefEqAccepts acceptance (applying the guarded mk field to the guard
        // premises) to DefEqJoinable a b, then eliminate that to DefEq a b.
        self.proofs.insert(
            "kernel_def_eq_reflects_spec".to_string(),
            ProofTerm::new(
                "kernel_def_eq_reflects_spec",
                concat!(
                    "fun (st : KernelState) (a : KExpr) (b : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelBinaryInputAdmissible st a b) ",
                    "(haccept : KernelDefEqAccepts st a b) => ",
                    "def_eq_joinable_reflects a b ",
                    "(KernelDefEqAccepts.rec st a b ",
                    "(fun (_h : KernelDefEqAccepts st a b) => DefEqJoinable a b) ",
                    "(fun (field : KernelStateEnvValid st -> ",
                    "KernelStateLocalCtxWellFormed st -> ",
                    "KernelBinaryInputAdmissible st a b -> DefEqJoinable a b) => ",
                    "field henv hctx hadm) ",
                    "haccept)"
                ),
                "Forward simulation for is_def_eq: eliminate KernelDefEqAccepts to DefEqJoinable, then to DefEq a b via def_eq_joinable_reflects. Skolem-free.",
            ),
        );
    }
}

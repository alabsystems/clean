// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-checker spec proof terms for the kernel ProofLibrary.
//!
//! Covers: type_checker_spec.rs DerivedPending definitions with value_src.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_type_checker_spec_proofs(&mut self) {
        // === tc_check_type_rule ===
        self.proofs.insert(
            "tc_check_type_rule".to_string(),
            ProofTerm::new(
                "tc_check_type_rule",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(hmatch : KernelStateMatchesSpec st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hcheck : KernelCheckAccepts st e T) => ",
                    "KernelCheckSound_summary st e T hmatch hadm hcheck"
                ),
                "Formal check_type rule: delegates to KernelCheckSound_summary.",
            ),
        );

        // === tc_infer_type_rule ===
        self.proofs.insert(
            "tc_infer_type_rule".to_string(),
            ProofTerm::new(
                "tc_infer_type_rule",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(hmatch : KernelStateMatchesSpec st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer : KernelInferAccepts st e T) => ",
                    "KernelInferSound_summary st e T hmatch hadm hinfer"
                ),
                "Formal infer_type rule: delegates to KernelInferSound_summary.",
            ),
        );

        // === tc_is_def_eq_rule ===
        self.proofs.insert(
            "tc_is_def_eq_rule".to_string(),
            ProofTerm::new(
                "tc_is_def_eq_rule",
                concat!(
                    "fun (st : KernelState) (e1 : KExpr) (e2 : KExpr) ",
                    "(hmatch : KernelStateMatchesSpec st) ",
                    "(hadm : KernelBinaryInputAdmissible st e1 e2) ",
                    "(hdefeq : KernelDefEqAccepts st e1 e2) => ",
                    "KernelDefEqSound_summary st e1 e2 hmatch hadm hdefeq"
                ),
                "Formal is_def_eq rule: delegates to KernelDefEqSound_summary.",
            ),
        );

        // === tc_check_completeness ===
        self.proofs.insert(
            "tc_check_completeness".to_string(),
            ProofTerm::new(
                "tc_check_completeness",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(_hmatch : KernelStateMatchesSpec st) ",
                    "(_hadm : KernelInputAdmissible st e) ",
                    "(hcheck : KernelCheckAccepts st e T) => ",
                    "KernelCheckAccepts.rec st e T ",
                    "(fun (_c : KernelCheckAccepts st e T) => CheckDecomp st e T) ",
                    "(fun (R : KExpr) ",
                    "(hpair : ProdType (KernelInferAccepts st e R) (KernelDefEqAccepts st R T)) ",
                    "(_hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st e -> KernelBinaryInputAdmissible st R T) => ",
                    "CheckDecomp.mk st e T R hpair) ",
                    "hcheck"
                ),
                "Check completeness: eliminate KernelCheckAccepts.rec (bind the inferred type R) and repackage into the CheckDecomp existential.",
            ),
        );

        // === tc_subject_reduction ===
        self.proofs.insert(
            "tc_subject_reduction".to_string(),
            ProofTerm::new(
                "tc_subject_reduction",
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) (e : KExpr) (T : KExpr) (e' : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(ht : has_type e T) (hred : whnf_to e e') => ",
                    "whnf_to_preserves_typing hf e e' T wd wr hred ht"
                ),
                "Subject reduction over the directed whnf_to relation: delegates to whnf_to_preserves_typing (the genuine forward subject reduction; #2859 retired the unsound symmetric is_def_eq form).",
            ),
        );

        // === tc_def_eq_transitivity ===
        self.proofs.insert(
            "tc_def_eq_transitivity".to_string(),
            ProofTerm::new(
                "tc_def_eq_transitivity",
                concat!(
                    "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h12 : is_def_eq e1 e2) (h23 : is_def_eq e2 e3) => ",
                    "def_eq_trans e1 e2 e3 h12 h23"
                ),
                "Transitivity of formal definitional equality: delegates to def_eq_trans. Part of #3221.",
            ),
        );

        // === tc_infer_type_correct ===
        self.proofs.insert(
            "tc_infer_type_correct".to_string(),
            ProofTerm::new(
                "tc_infer_type_correct",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(hstate : KernelStateMatchesSpec st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer : KernelInferAccepts st e T) => ",
                    "KernelInferSound_summary st e T hstate hadm hinfer"
                ),
                "Algorithmic infer_type correctness: delegates to KernelInferSound_summary. Part of #3221.",
            ),
        );
    }
}

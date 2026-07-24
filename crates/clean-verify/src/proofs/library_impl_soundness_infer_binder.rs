// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implementation soundness infer refinement proof terms for binder cases.
//!
//! Contains proof terms for:
//! - Binder sound: kernel_infer_lam_sound, kernel_infer_pi_sound
//!   (eliminate Lam/PiInferWitness into the skolem-free has_type),
//!   infer_sound_at_lam, infer_sound_at_pi
//!
//! The former skolem-named typing-step projections (kernel_infer_lam_domain_sort,
//! kernel_infer_lam_body_typing, kernel_infer_lam_result_step,
//! kernel_infer_pi_domain_sort, kernel_infer_pi_codomain_sort,
//! kernel_infer_pi_imax_result_step) are RETIRED — their types named the six
//! retired infer Skolems, now bound internally by Lam/PiInferWitness.
//!
//! Split from library_impl_soundness_infer.rs for file-size compliance.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_impl_soundness_infer_binder_proofs(&mut self) {
        // kernel_infer_lam_body_step / kernel_infer_pi_body_step RETIRED
        // (census 18->16): dead-end ProdType.fst projections of the vestigial
        // KernelLam/PiBodyAdmissible guards, consumed by nothing.

        // =================================================================
        // Binder sound (implementation_soundness_infer_refinement_binder_sound.rs)
        // =================================================================

        self.proofs.insert(
            "kernel_infer_lam_sound".to_string(),
            ProofTerm::new(
                "kernel_infer_lam_sound",
                concat!(
                    "fun (st : KernelState) (A : KExpr) (body : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.lam A body)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.lam A body) T) => ",
                    "LamInferDecomp.rec st A body T ",
                    "(fun (_d : LamInferDecomp st A body T) => has_type (KExpr.lam A body) T) ",
                    "(fun (bt : KExpr) (hbody_infer : KernelInferAccepts st body bt) ",
                    "(hwit : LamInferWitness A body bt T) => ",
                    "LamInferWitness.rec A body bt T ",
                    "(fun (_w : LamInferWitness A body bt T) => has_type (KExpr.lam A body) T) ",
                    "(fun (dl : Level) ",
                    "(hdom : Typing A (KExpr.sort dl)) ",
                    "(hbody : Typing body bt) ",
                    "(hresult : Eq KExpr (KExpr.pi A bt) T) => ",
                    "raw_type_conversion (KExpr.lam A body) (KExpr.pi A bt) T ",
                    "(Typing.lam A body bt dl hdom hbody) ",
                    "(def_eq_eq_right (KExpr.pi A bt) (KExpr.pi A bt) T ",
                    "(DefEq.refl (KExpr.pi A bt)) hresult)) ",
                    "hwit) ",
                    "(kernel_infer_lam_decomposition st A body T hinfer)"
                ),
                concat!(
                    "Constructive lam-case infer_type local bridge: eliminate ",
                    "LamInferWitness (body-type/domain-level retired) into the ",
                    "skolem-free has_type via Typing.lam and raw_type_conversion. ",
                    "Part of #2869, #461."
                ),
            ),
        );

        self.proofs.insert(
            "kernel_infer_pi_sound".to_string(),
            ProofTerm::new(
                "kernel_infer_pi_sound",
                concat!(
                    "fun (st : KernelState) (A : KExpr) (B : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.pi A B)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.pi A B) T) => ",
                    "PiInferWitness.rec A B T ",
                    "(fun (_w : PiInferWitness A B T) => has_type (KExpr.pi A B) T) ",
                    "(fun (dom : Level) (cod : Level) ",
                    "(hdom : Typing A (KExpr.sort dom)) ",
                    "(hcod : Typing B (KExpr.sort cod)) ",
                    "(hresult : Eq KExpr (KExpr.sort (Level.imax dom cod)) T) => ",
                    "raw_type_conversion (KExpr.pi A B) (KExpr.sort (Level.imax dom cod)) T ",
                    "(Typing.pi A B dom cod hdom hcod) ",
                    "(def_eq_eq_right (KExpr.sort (Level.imax dom cod)) (KExpr.sort (Level.imax dom cod)) T ",
                    "(DefEq.refl (KExpr.sort (Level.imax dom cod))) hresult)) ",
                    "(kernel_infer_pi_decomposition st A B T hinfer)"
                ),
                concat!(
                    "Constructive pi-case infer_type local bridge: eliminate ",
                    "PiInferWitness (domain/codomain levels retired) into the ",
                    "skolem-free has_type via Typing.pi and raw_type_conversion. ",
                    "Part of #2869, #461."
                ),
            ),
        );

        self.proofs.insert(
            "infer_sound_at_lam".to_string(),
            ProofTerm::new(
                "infer_sound_at_lam",
                concat!(
                    "fun (A : KExpr) (body : KExpr) ",
                    "(_ihA : InferSoundAt A) (_ihbody : InferSoundAt body) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.lam A body)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.lam A body) T) => ",
                    "kernel_infer_lam_sound st A body T henv hctx hadm hinfer"
                ),
                concat!(
                    "KExpr.rec lam-case handler for InferSoundAt motive. Delegates ",
                    "to kernel_infer_lam_sound; IH terms unused. Part of #461."
                ),
            ),
        );

        self.proofs.insert(
            "infer_sound_at_pi".to_string(),
            ProofTerm::new(
                "infer_sound_at_pi",
                concat!(
                    "fun (A : KExpr) (B : KExpr) ",
                    "(_ihA : InferSoundAt A) (_ihB : InferSoundAt B) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.pi A B)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.pi A B) T) => ",
                    "kernel_infer_pi_sound st A B T henv hctx hadm hinfer"
                ),
                concat!(
                    "KExpr.rec pi-case handler for InferSoundAt motive. Delegates ",
                    "to kernel_infer_pi_sound; IH terms unused. Part of #461."
                ),
            ),
        );
    }
}

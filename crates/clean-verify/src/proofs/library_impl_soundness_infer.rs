// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implementation soundness infer refinement proof terms for the kernel ProofLibrary.
//!
//! Contains proof terms for:
//! - Sort case: kernel_infer_sort_sound
//! - Dispatch: infer_sound_at_sort, infer_sound_at_const, infer_sound_at_let,
//!   kernel_infer_returns_well_typed
//! - App steps: kernel_infer_app_fun_step, kernel_infer_app_pi_step,
//!   kernel_infer_app_arg_check_step, kernel_infer_app_result_step
//! - App sound: kernel_infer_app_sound, infer_sound_at_app
//!
//! Binder-related proof terms are in library_impl_soundness_infer_binder.rs.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_impl_soundness_infer_proofs(&mut self) {
        // =================================================================
        // Sort case (implementation_soundness_infer_refinement.rs)
        // =================================================================

        self.proofs.insert(
            "kernel_infer_sort_sound".to_string(),
            ProofTerm::new(
                "kernel_infer_sort_sound",
                concat!(
                    "fun (st : KernelState) (l : Level) (T : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hinfer : KernelInferAccepts st (KExpr.sort l) T) => ",
                    "Eq.substType KExpr (fun (X : KExpr) => Typing (KExpr.sort l) X) ",
                    "(KExpr.sort (Level.succ l)) T ",
                    "(kernel_infer_sort_result st l T hinfer) ",
                    "(Typing.sort l)"
                ),
                concat!(
                    "Forward simulation for the sort case: kernel inference on Sort(l) ",
                    "yields has_type (Sort l) T. Constructive proof via exact-result ",
                    "axiom and Typing.sort. Part of #461."
                ),
            ),
        );

        // =================================================================
        // Dispatch (implementation_soundness_infer_refinement_dispatch.rs)
        // =================================================================

        self.proofs.insert(
            "infer_sound_at_sort".to_string(),
            ProofTerm::new(
                "infer_sound_at_sort",
                concat!(
                    "fun (l : Level) (st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(_hadm : KernelInputAdmissible st (KExpr.sort l)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.sort l) T) => ",
                    "kernel_infer_sort_sound st l T henv hctx hinfer"
                ),
                concat!(
                    "KExpr.rec sort-case handler for the InferSoundAt motive. ",
                    "Delegates to kernel_infer_sort_sound. Part of #461."
                ),
            ),
        );

        self.proofs.insert(
            "infer_sound_at_const".to_string(),
            ProofTerm::new(
                "infer_sound_at_const",
                concat!(
                    "fun (n : Name) (us : ListType Level) (st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.const n us)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.const n us) T) => ",
                    "kernel_infer_const_sound st n us T henv hctx hadm hinfer"
                ),
                concat!(
                    "KExpr.rec const-case handler for the InferSoundAt motive. ",
                    "Delegates to kernel_infer_const_sound. Part of #2895, #461."
                ),
            ),
        );

        // infer_sound_at_let: KExpr.rec let_-case handler (trailing minor after
        // const). KernelInferAccepts has NO let_ constructor, so — exactly like
        // the bvar case — an acceptance witness at a let is uninhabited: the
        // master inversion reduces InferInversionAt to Empty at a let and the
        // case is discharged by Empty.rec. Mirrors the spec definition in
        // implementation_soundness_infer_refinement_dispatch.rs.
        self.proofs.insert(
            "infer_sound_at_let".to_string(),
            ProofTerm::new(
                "infer_sound_at_let",
                concat!(
                    "fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(_ihty : InferSoundAt ty) (_ihval : InferSoundAt val) ",
                    "(_ihbody : InferSoundAt body) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(_hadm : KernelInputAdmissible st (KExpr.let_ ty val body)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.let_ ty val body) T) => ",
                    "Empty.rec (fun (_ : Empty) => has_type (KExpr.let_ ty val body) T) ",
                    "(kernel_infer_inversion st (KExpr.let_ ty val body) T hinfer)"
                ),
                concat!(
                    "KExpr.rec let_-case handler for the InferSoundAt motive. ",
                    "KernelInferAccepts has no let_ constructor, so the acceptance ",
                    "witness is uninhabited and the case is discharged by Empty.rec ",
                    "(same vacuous shape as the bvar case). Part of #461."
                ),
            ),
        );

        self.proofs.insert(
            "kernel_infer_returns_well_typed".to_string(),
            ProofTerm::new(
                "kernel_infer_returns_well_typed",
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer : KernelInferAccepts st e T) => ",
                    "KExpr.rec InferSoundAt ",
                    "infer_sound_at_sort infer_sound_at_bvar ",
                    "infer_sound_at_app infer_sound_at_lam infer_sound_at_pi infer_sound_at_const ",
                    "infer_sound_at_let ",
                    "e st T henv hctx hadm hinfer"
                ),
                concat!(
                    "Forward simulation contract for infer_type: successful kernel ",
                    "inference implies the specification typing judgment. Proof via ",
                    "KExpr.rec with InferSoundAt motive (seven minors, trailing ",
                    "let_ case vacuous). Part of #461."
                ),
            ),
        );

        // =================================================================
        // App steps (implementation_soundness_infer_refinement_app.rs)
        // =================================================================

        // kernel_infer_app_fun_step is RETIRED (KernelInferResult un-Skolemization):
        // its type named the inferred function type as the Skolem KernelInferResult
        // st f, which no longer exists (the inferred subtypes Rf/Ra are bound
        // existentially inside AppInferDecomp). Along with the earlier-retired
        // kernel_infer_app_pi_step / kernel_infer_app_arg_check_step /
        // kernel_infer_app_result_step, its evidence is recovered directly inside
        // kernel_infer_app_sound by eliminating AppInferDecomp (bind Rf/Ra) then
        // AppInferWitness (bind dom/cod).

        // =================================================================
        // App sound (implementation_soundness_infer_refinement_app_sound.rs)
        // =================================================================

        self.proofs.insert(
            "kernel_infer_app_sound".to_string(),
            ProofTerm::new(
                "kernel_infer_app_sound",
                concat!(
                    "fun (st : KernelState) (f : KExpr) (a : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.app f a)) ",
                    "(hfun_sound : forall (Tf : KExpr), KernelInferAccepts st f Tf -> has_type f Tf) ",
                    "(harg_sound : forall (Ta : KExpr), KernelInferAccepts st a Ta -> has_type a Ta) ",
                    "(hinfer : KernelInferAccepts st (KExpr.app f a) T) => ",
                    "AppInferDecomp.rec st f a T ",
                    "(fun (_d : AppInferDecomp st f a T) => has_type (KExpr.app f a) T) ",
                    "(fun (Rf : KExpr) (Ra : KExpr) ",
                    "(hf : KernelInferAccepts st f Rf) ",
                    "(ha : KernelInferAccepts st a Ra) ",
                    "(hwit : AppInferWitness st Rf Ra a T) ",
                    "(hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st (KExpr.app f a) -> ",
                    "KernelInputAdmissible st Rf) => ",
                    "AppInferWitness.rec st Rf Ra a T ",
                    "(fun (_w : AppInferWitness st Rf Ra a T) => has_type (KExpr.app f a) T) ",
                    "(fun (dom : KExpr) (cod : KExpr) ",
                    "(hwhnf : KernelWhnfAccepts st Rf (KExpr.pi dom cod)) ",
                    "(hdefeq : KernelDefEqAccepts st Ra dom) ",
                    "(hresult : Eq KExpr (instantiate cod a) T) ",
                    "(hchkadm : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st a -> ",
                    "KernelBinaryInputAdmissible st Ra dom) => ",
                    "raw_type_conversion (KExpr.app f a) (instantiate cod a) T ",
                    "(Typing.app f a dom cod ",
                    "(raw_type_conversion f Rf (KExpr.pi dom cod) ",
                    "(hfun_sound Rf hf) ",
                    "(kernel_whnf_returns_def_eq st Rf (KExpr.pi dom cod) ",
                    "henv hctx ",
                    "(hguard henv hctx hadm) ",
                    "hwhnf)) ",
                    "(kernel_check_returns_well_typed_from_infer st a dom henv hctx ",
                    "(kernel_input_admissible_app_arg st f a hadm) ",
                    "harg_sound ",
                    "(KernelCheckAccepts.mk st a dom Ra ",
                    "(ProdType.mk (KernelInferAccepts st a Ra) ",
                    "(KernelDefEqAccepts st Ra dom) ",
                    "ha hdefeq) ",
                    "hchkadm))) ",
                    "(def_eq_eq_right (instantiate cod a) (instantiate cod a) T ",
                    "(DefEq.refl (instantiate cod a)) hresult)) ",
                    "hwit) ",
                    "(kernel_infer_app_decomposition st f a T hinfer)"
                ),
                concat!(
                    "Constructive app-case infer_type local bridge: eliminates the ",
                    "AppInferDecomp existential (inferred subtypes Rf/Ra — KernelInferResult ",
                    "retired) then the AppInferWitness packaged existential (pi domain/codomain) ",
                    "into the skolem-free has_type via the WHNF bridge on Rf and the local check ",
                    "bridge (KernelCheckAccepts.mk over the arg-infer acceptance at Ra). ",
                    "Part of #461."
                ),
            ),
        );

        self.proofs.insert(
            "infer_sound_at_app".to_string(),
            ProofTerm::new(
                "infer_sound_at_app",
                concat!(
                    "fun (f : KExpr) (a : KExpr) ",
                    "(ihf : InferSoundAt f) (iha : InferSoundAt a) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.app f a)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.app f a) T) => ",
                    "kernel_infer_app_sound st f a T henv hctx hadm ",
                    "(fun (Tf : KExpr) (haccf : KernelInferAccepts st f Tf) => ",
                    "ihf st Tf henv hctx ",
                    "(kernel_input_admissible_app_fun st f a hadm) haccf) ",
                    "(fun (Ta : KExpr) (hacca : KernelInferAccepts st a Ta) => ",
                    "iha st Ta henv hctx ",
                    "(kernel_input_admissible_app_arg st f a hadm) hacca) ",
                    "hinfer"
                ),
                concat!(
                    "KExpr.rec app-case handler for InferSoundAt motive. Uses IH ",
                    "terms ihf/iha with admissibility inversions to supply ",
                    "kernel_infer_app_sound parameters. Part of #461."
                ),
            ),
        );
    }
}

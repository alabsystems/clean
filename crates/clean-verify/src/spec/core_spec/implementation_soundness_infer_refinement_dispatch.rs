// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Infer_type dispatch: KExpr.rec case split via InferSoundAt motive (#461).
//!
//! The dispatch uses InferSoundAt (a named semireducible motive defined in the
//! refinement root) to avoid the inline motive beta-reduction that caused the
//! Discriminant(6) vs (3) mismatch. Each KExpr constructor case is a thin
//! wrapper adapting the per-case sound theorem to the KExpr.rec expected
//! signature.
//!
//! Proof structure:
//!   KExpr.rec InferSoundAt
//!     sort case  → infer_sound_at_sort (delegates to kernel_infer_sort_sound)
//!     bvar case  → infer_sound_at_bvar (bvar_not_closed → Empty.rec)
//!     app case   → infer_sound_at_app  (uses IH for f and a)
//!     lam case   → infer_sound_at_lam  (delegates to kernel_infer_lam_sound)
//!     pi case    → infer_sound_at_pi   (delegates to kernel_infer_pi_sound)
//!     const case → infer_sound_at_const (delegates to kernel_infer_const_sound)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement_dispatch(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // Per-case dispatch wrappers (KExpr.rec case handlers)
        // =========================================================
        //
        // Each wrapper adapts a per-case sound theorem to the type
        // signature expected by KExpr.rec with motive InferSoundAt:
        //   sort: (l : Level) -> InferSoundAt (KExpr.sort l)
        //   bvar: (n : Nat) -> InferSoundAt (KExpr.bvar n)
        //   app:  (f a : KExpr) -> InferSoundAt f -> InferSoundAt a
        //                       -> InferSoundAt (KExpr.app f a)
        //   lam:  (A body : KExpr) -> InferSoundAt A -> InferSoundAt body
        //                          -> InferSoundAt (KExpr.lam A body)
        //   pi:   (A B : KExpr) -> InferSoundAt A -> InferSoundAt B
        //                       -> InferSoundAt (KExpr.pi A B)
        //   const: (n : Name) -> (us : ListType Level)
        //                        -> InferSoundAt (KExpr.const n us)
        //   let_: (ty val body : KExpr) -> InferSoundAt ty -> InferSoundAt val
        //                        -> InferSoundAt body -> InferSoundAt (KExpr.let_ ty val body)

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_sort".to_string(),
            type_src: "forall (l : Level), InferSoundAt (KExpr.sort l)".to_string(),
            value_src: Some(
                concat!(
                    "fun (l : Level) (st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(_hadm : KernelInputAdmissible st (KExpr.sort l)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.sort l) T) => ",
                    "kernel_infer_sort_sound st l T henv hctx hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "KExpr.rec sort-case handler for the InferSoundAt motive. ",
                "Delegates to kernel_infer_sort_sound, dropping the unused ",
                "admissibility premise (sorts are trivially admissible). ",
                "Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_sort_sound".to_string(),
            ])),
            // kernel_infer_sort_result is no longer an axiom leaf (derived via
            // kernel_infer_inversion); expand through to the master inversion's
            // residual closure: 10 infer-band skolems + KernelCheckAccepts.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_bvar".to_string(),
            type_src: "forall (n : Nat), InferSoundAt (KExpr.bvar n)".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (st : KernelState) (T : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.bvar n)) ",
                    "(_hinfer : KernelInferAccepts st (KExpr.bvar n) T) => ",
                    "Empty.rec (fun (_ : Empty) => has_type (KExpr.bvar n) T) ",
                    "(bvar_not_closed n hadm)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "KExpr.rec bvar-case handler for the InferSoundAt motive. ",
                "A closed bvar is impossible (bvar_not_closed yields Empty), ",
                "so the case is discharged by Empty.rec. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "bvar_not_closed".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // infer_sound_at_app, infer_sound_at_lam, infer_sound_at_pi are registered
        // in their home modules (app, binder_typing respectively) because their
        // value_src references per-case sound theorems from those modules.

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_const".to_string(),
            type_src: "forall (n : Name) (us : ListType Level), InferSoundAt (KExpr.const n us)"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Name) (us : ListType Level) (st : KernelState) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.const n us)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.const n us) T) => ",
                    "kernel_infer_const_sound st n us T henv hctx hadm hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "KExpr.rec const-case handler for the InferSoundAt motive. Delegates to kernel_infer_const_sound. Part of #2895, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_const_sound".to_string(),
            ])),
            // kernel_infer_const_sound is no longer an axiom leaf (derived via
            // kernel_infer_inversion); expand through to the master inversion's
            // residual closure: 10 infer-band skolems + KernelCheckAccepts.
            axiom_deps: HashSet::new(),
        })?;

        // infer_sound_at_let: KExpr.rec let_-case handler for the InferSoundAt
        // motive. KernelInferAccepts has NO let_ constructor — the real kernel's
        // Let arm is outside the core KExpr fragment the infer model covers
        // (sort/bvar/app/lam/pi/const only), so an acceptance witness at a let is
        // uninhabited, exactly like the bvar case. The master inversion
        // kernel_infer_inversion at a let reduces InferInversionAt to Empty (the
        // let_ minor of that semireducible motive returns Empty, mirroring bvar),
        // so the case is discharged by Empty.rec — the vacuous/reject shape, with
        // the let_ ctor's three recursive fields (ty, val, body) and their three
        // (unused) InferSoundAt IHs.
        self.add_definition(SpecDefinition {
            name: "infer_sound_at_let".to_string(),
            type_src: concat!(
                "forall (ty : KExpr) (val : KExpr) (body : KExpr), ",
                "InferSoundAt ty -> InferSoundAt val -> InferSoundAt body -> ",
                "InferSoundAt (KExpr.let_ ty val body)"
            )
            .to_string(),
            value_src: Some(
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
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "KExpr.rec let_-case handler for the InferSoundAt motive. ",
                "KernelInferAccepts has no let_ constructor (Let is outside the ",
                "core KExpr fragment the infer model covers), so an acceptance ",
                "witness at a let is uninhabited — the master inversion reduces ",
                "InferInversionAt to Empty at a let, discharging the case by ",
                "Empty.rec (the same vacuous shape as the bvar case). Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
                "KernelInferAccepts".to_string(),
                "Empty.rec".to_string(),
            ])),
            // Inherits the master inversion's residual closure (reached through
            // kernel_infer_inversion): EMPTY after the KernelInferResult
            // un-Skolemization.
            axiom_deps: HashSet::new(),
        })?;

        // infer_sound_at_proj / infer_sound_at_lit: KExpr.rec proj/lit-case
        // handlers. Proj and lit are outside the core KExpr fragment the infer
        // model covers (like let_/bvar), so KernelInferAccepts has no proj/lit
        // constructor — kernel_infer_inversion reduces InferInversionAt to Empty
        // at proj/lit, discharging both cases by Empty.rec (proj/lit rung).
        self.add_definition(SpecDefinition {
            name: "infer_sound_at_proj".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub : KExpr), ",
                "InferSoundAt sub -> InferSoundAt (KExpr.proj s i sub)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : InferSoundAt sub) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(_hadm : KernelInputAdmissible st (KExpr.proj s i sub)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.proj s i sub) T) => ",
                    "Empty.rec (fun (_ : Empty) => has_type (KExpr.proj s i sub) T) ",
                    "(kernel_infer_inversion st (KExpr.proj s i sub) T hinfer)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "KExpr.rec proj-case handler for InferSoundAt. KernelInferAccepts has no proj constructor (outside the core infer fragment), so acceptance is uninhabited — kernel_infer_inversion reduces to Empty, discharged by Empty.rec. Proj/lit rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
                "KernelInferAccepts".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "infer_sound_at_lit".to_string(),
            type_src: "forall (v : Nat), InferSoundAt (KExpr.lit v)".to_string(),
            value_src: Some(
                concat!(
                    "fun (v : Nat) ",
                    "(st : KernelState) (T : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(_hadm : KernelInputAdmissible st (KExpr.lit v)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.lit v) T) => ",
                    "Empty.rec (fun (_ : Empty) => has_type (KExpr.lit v) T) ",
                    "(kernel_infer_inversion st (KExpr.lit v) T hinfer)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "KExpr.rec lit-case handler for InferSoundAt. KernelInferAccepts has no lit constructor, so acceptance is uninhabited — kernel_infer_inversion reduces to Empty, discharged by Empty.rec. Proj/lit rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InferSoundAt".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
                "KernelInferAccepts".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Top-level dispatch: kernel_infer_returns_well_typed
        // =========================================================
        //
        // The proof term uses KExpr.rec with the named InferSoundAt motive
        // and the six per-case wrappers above. After applying KExpr.rec to
        // expression e, the result has type InferSoundAt e, which unfolds to
        // the full soundness proposition. The remaining arguments (st, T,
        // henv, hctx, hadm, hinfer) are passed through to complete the proof.
        //
        // Using a named motive avoids the inline lambda beta-reduction that
        // caused the Discriminant(6) vs (3) mismatch in previous attempts.

        self.add_definition(SpecDefinition {
            name: "kernel_infer_returns_well_typed".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelInferAccepts st e T -> ",
                "has_type e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer : KernelInferAccepts st e T) => ",
                    "KExpr.rec InferSoundAt ",
                    "infer_sound_at_sort infer_sound_at_bvar ",
                    "infer_sound_at_app infer_sound_at_lam infer_sound_at_pi infer_sound_at_const ",
                    "infer_sound_at_let infer_sound_at_proj infer_sound_at_lit ",
                    "e st T henv hctx hadm hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Forward simulation contract for infer_type: successful kernel inference ",
                "implies the specification typing judgment. Proof via KExpr.rec with ",
                "InferSoundAt motive, dispatching to per-case wrappers that delegate ",
                "to the constructive sound theorems in the sort/bvar (root), app, and ",
                "binder modules. The BVar case is discharged constructively from the ",
                "closedness precondition (bvar_not_closed). Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "InferSoundAt".to_string(),
                "infer_sound_at_sort".to_string(),
                "infer_sound_at_bvar".to_string(),
                "infer_sound_at_app".to_string(),
                "infer_sound_at_lam".to_string(),
                "infer_sound_at_pi".to_string(),
                "infer_sound_at_const".to_string(),
                "infer_sound_at_let".to_string(),
                "infer_sound_at_proj".to_string(),
                "infer_sound_at_lit".to_string(),
            ])),
            // The six per-case infer axioms (sort_result, const_sound,
            // app_decomposition, app_fun_type_admissible, lam_decomposition,
            // pi_decomposition) are no longer axiom leaves — all are derived
            // from the faithful KernelInferAccepts inductive via
            // kernel_infer_inversion. The remaining leaves are the master
            // inversion's residual closure (10 infer-band skolems +
            // KernelCheckAccepts) plus the check/defeq band the app case
            // routes through.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_refinement_dispatch_tests.rs"]
mod implementation_soundness_infer_refinement_dispatch_tests;

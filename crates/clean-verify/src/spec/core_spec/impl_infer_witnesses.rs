// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Non-vacuity witnesses for `ImplInfer` — one per rule (job C1's acceptance
//! gate), plus the flagship `λ(x : Prop). x` derivation.
//!
//! # Why a witness per rule is the gate, not a nicety
//!
//! The measured failure this whole lane replaces is a relation whose arms were
//! *uninhabited or content-free*: `KernelInferAccepts.const`'s only field is a
//! guarded `has_type (const n us) T`, which `const_untypable` refutes — so in
//! valid states that arm is uninhabited while its consumer reported
//! `DerivedProved`. `.lam` / `.pi` carry exactly `Typing.lam` / `Typing.pi`'s
//! own premises inside a witness type, and `typable_bvar_ceiling_zero` then
//! forces every inhabitant closed. A relation can be perfectly well-formed,
//! type-check, and mean nothing.
//!
//! Every witness below is a **pure constructor application** with zero
//! `axiom_deps`: each premise is discharged by `Eq.refl` (i.e. the modelled
//! operation actually COMPUTES to the required value), so the witnesses double
//! as executable checks that `lctx_lookup`, `impl_open`, `impl_abstract_fvar`,
//! `impl_subst_fvar`, `impl_inst_levels`, `level_params_ok` and `impl_lit_type`
//! all reduce as intended.
//!
//! # The flagship
//!
//! `implinfer_lam_identity_witness` derives
//!
//! ```text
//! ImplInfer  0  []  (λ(x : Prop). x)  ((x : Prop) → Prop)  1
//! ```
//!
//! — **the exact acceptance `KernelInferAccepts` cannot represent.** Model B's
//! `Lam` arm recursively accepts the raw de Bruijn body *in the same state*, so
//! its lam inversion extracts `KernelInferAccepts st (bvar 0) bt`, which
//! `kernel_infer_bvar_empty` makes `Empty`. Here the binder is OPENED to
//! `FVar(0)` under an extended `LCtx` exactly as `tc/infer.rs:533-548` does, the
//! body is inferred by the `fvar` rule, and the result type is abstracted back.
//! Both the deployed kernel and the layer-2 models that have a variable rule
//! (`KernelInfers`, `TypingCtxConv`) accept this term — but NOT the degenerate
//! env-free `Typing`, which has no bvar rule; that is a separate defect, not the
//! one this witness answers. Now the
//! layer-1 relation does too.
//!
//! ZERO new axioms; every definition here is `DerivedProved` with an empty
//! axiom closure.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// The empty constant environment, spelled inline everywhere (a named
/// definition would risk an opaque-unfolding wall in the witness types; the
/// `kernelinfers_sort_witness` precedent inlines its `tenv` the same way).
const EMPTY_TENV: &str = "(fun (nm : Name) => OptionType.none ImplConstInfo)";

/// No declared universe parameters — so `check_level` demands every level be
/// param-free, which is exactly the situation for a closed `Sort` term.
const NO_LPS: &str = "(ListType.nil Name)";

/// `BinderData { info: Default, mult: Many }` — what `BinderInfo::Default.into()`
/// produces, and what `ctx_push_let` (`tc/config.rs:48`) stores through
/// `LocalContext::push_let` (`tc/local_context.rs:126`).
const BD: &str = "(BinderData.mk BinderInfo.default Multiplicity.many)";

impl Specification {
    /// C1 acceptance gate: a non-vacuity witness for every `ImplInfer` rule.
    pub(super) fn add_impl_infer_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_impl_witness_leaves()?;
        self.add_impl_witness_binders()?;
        Ok(())
    }

    /// The non-recursive rules: sort, fvar, const, lit (both literal kinds),
    /// mdata.
    fn add_impl_witness_leaves(&mut self) -> Result<(), SpecError> {
        // ── sort ────────────────────────────────────────────────────────────
        // (Prop : Type) in the empty context, with check_level discharged by
        // computation: level_params_ok [] Level.zero reduces to Bool.true.
        self.add_definition(SpecDefinition {
            name: "implinfer_sort_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.sort Level.zero) (ImplExpr.sort (Level.succ Level.zero)) Nat.zero"
            ),
            value_src: Some(format!(
                "ImplInfer.sort {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil Level.zero \
                 (Eq.refl Bool Bool.true)"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the sort rule: (Prop : Type) in the empty \
                          context with no declared level params. The check_level premise is \
                          discharged by Eq.refl — level_params_ok [] Level.zero COMPUTES to \
                          Bool.true — so this also proves the modelled check_level reduces. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "level_params_ok".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── fvar ────────────────────────────────────────────────────────────
        // A free variable in a one-entry context returns its stored type
        // UNLIFTED — the visible layer-1/layer-2 difference (KernelInfers.bvar
        // and TypingCtxConv.var both apply lift_at A 0 (succ i)).
        let g1 = format!(
            "(LCtx.snoc LCtx.nil (LocalDecl.mk Nat.zero (ImplExpr.sort Level.zero) \
             (OptionType.none ImplExpr) {BD}))"
        );
        self.add_definition(SpecDefinition {
            name: "implinfer_fvar_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) {g1} \
                 (ImplExpr.fvar Nat.zero) (ImplExpr.sort Level.zero) (Nat.succ Nat.zero)"
            ),
            value_src: Some(format!(
                "ImplInfer.fvar {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) {g1} Nat.zero \
                 (ImplExpr.sort Level.zero) \
                 (Eq.refl (OptionType ImplExpr) (OptionType.some ImplExpr (ImplExpr.sort Level.zero)))"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the fvar rule: FVar(0) in the one-entry \
                          context [0 : Prop] infers Prop. The lookup premise is discharged by \
                          Eq.refl, so lctx_lookup genuinely COMPUTES the entry by FVarId. The \
                          returned type is UNLIFTED — the concrete point where layer 1 differs \
                          from KernelInfers.bvar / TypingCtxConv.var, both of which apply \
                          lift_at A 0 (succ i). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "lctx_lookup".to_string(),
                "LocalDecl".to_string(),
                "LCtx".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── const ───────────────────────────────────────────────────────────
        // ALL FIVE operations of the release Const arm fire, each discharged by
        // computation: env lookup, level arity, per-level check_level, the
        // unsafe gate, the partial gate. Model B's const arm models ZERO of
        // these — this witness is the direct measure of the difference.
        let ci = "(ImplConstInfo.mk (ListType.nil Name) (ImplExpr.sort Level.zero) Bool.false Bool.false)";
        let tenv1 = format!("(fun (nm : Name) => OptionType.some ImplConstInfo {ci})");
        self.add_definition(SpecDefinition {
            name: "implinfer_const_witness".to_string(),
            type_src: format!(
                "ImplInfer {tenv1} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.const Name.anonymous (ListType.nil Level)) \
                 (impl_inst_levels (impl_const_lps {ci}) (ListType.nil Level) (impl_const_type {ci})) \
                 Nat.zero"
            ),
            value_src: Some(format!(
                "ImplInfer.const {tenv1} {NO_LPS} Nat.zero LCtx.nil Name.anonymous \
                 (ListType.nil Level) {ci} \
                 (Eq.refl (OptionType ImplConstInfo) (OptionType.some ImplConstInfo {ci})) \
                 (Eq.refl Nat Nat.zero) \
                 (Eq.refl Bool Bool.true) \
                 (Eq.refl Bool Bool.false) \
                 (Eq.refl Bool Bool.false)"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the const rule, exercising ALL FIVE \
                          operations the release Const arm performs (tc/infer.rs:371-424): \
                          get_const lookup, level-arity equality, per-level check_level, the \
                          is_unsafe gate and the is_partial gate — every one discharged by \
                          Eq.refl, i.e. by actual computation. The stated result is the RAW \
                          constructor conclusion (impl_inst_levels applied to the record's own \
                          fields), so instantiate_level_params is exercised too. Contrast \
                          KernelInferAccepts.const, whose single field is a guarded \
                          `has_type (const n us) T` — modelling ZERO of the five, and \
                          UNINHABITED in valid states because const_untypable refutes it. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplConstInfo".to_string(),
                "impl_inst_levels".to_string(),
                "impl_const_lps".to_string(),
                "impl_const_type".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── lit, both kinds ─────────────────────────────────────────────────
        for (name, ctor, doc) in [
            (
                "implinfer_lit_nat_witness",
                "(ImplLit.natVal Nat.zero)",
                "Literal::Nat",
            ),
            (
                "implinfer_lit_str_witness",
                "(ImplLit.strVal Nat.zero)",
                "Literal::String",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                     (ImplExpr.lit {ctor}) (impl_lit_type {ctor}) Nat.zero"
                ),
                value_src: Some(format!(
                    "ImplInfer.lit {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil {ctor}"
                )),
                is_axiom: false,
                description: format!(
                    "Non-vacuity witness for the lit rule at {doc}. Pure constructor \
                     application: the arm performs ZERO environment validation \
                     (tc/infer.rs:647-650), so the rule has no premise and the witness has \
                     nothing to discharge — which is itself the faithful statement. \
                     Zero axiom_deps."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "ImplInfer".to_string(),
                    "ImplLit".to_string(),
                    "impl_lit_type".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // ── mdata ───────────────────────────────────────────────────────────
        self.add_definition(SpecDefinition {
            name: "implinfer_mdata_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.mdata (ImplExpr.sort Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) Nat.zero"
            ),
            value_src: Some(format!(
                "ImplInfer.mdata {EMPTY_TENV} {NO_LPS} Nat.zero Nat.zero LCtx.nil \
                 (ImplExpr.sort Level.zero) (ImplExpr.sort (Level.succ Level.zero)) \
                 implinfer_sort_witness"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the mdata rule: metadata is fully \
                          transparent — same type, same next_id, one recursive premise \
                          (tc/infer.rs:657-663). Consumes implinfer_sort_witness, so it also \
                          demonstrates the relation composes. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "implinfer_sort_witness".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The binder rules (lam, pi, let_) and the application rule — the four
    /// that exercise open/abstract, the fresh-id discipline and the operational
    /// boundary relations.
    fn add_impl_witness_binders(&mut self) -> Result<(), SpecError> {
        let g1 = format!(
            "(LCtx.snoc LCtx.nil (LocalDecl.mk Nat.zero (ImplExpr.sort Level.zero) \
             (OptionType.none ImplExpr) {BD}))"
        );

        // ── lam: THE FLAGSHIP — λ(x : Prop). x ──────────────────────────────
        // Fresh id 0 is minted, pushed as [0 : Prop], the body BVar(0) is OPENED
        // to FVar(0), the fvar rule infers Prop, and Prop is abstracted back out
        // (vacuously — it contains no FVar(0)). next_id 0 -> 1.
        //
        // This is the acceptance KernelInferAccepts provably cannot represent.
        self.add_definition(SpecDefinition {
            name: "implinfer_lam_identity_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.lam {BD} (ImplExpr.sort Level.zero) (ImplExpr.bvar Nat.zero)) \
                 (ImplExpr.pi {BD} (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero)) \
                 (Nat.succ Nat.zero)"
            ),
            value_src: Some(format!(
                "ImplInfer.lam {EMPTY_TENV} {NO_LPS} Nat.zero Nat.zero (Nat.succ Nat.zero) \
                 LCtx.nil {BD} (ImplExpr.sort Level.zero) (ImplExpr.bvar Nat.zero) \
                 (ImplExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero) \
                 (ImplExpr.sort Level.zero) \
                 implinfer_sort_witness \
                 (ImplWhnfTo.done (ImplExpr.sort (Level.succ Level.zero))) \
                 (ImplInfer.fvar {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) {g1} Nat.zero \
                 (ImplExpr.sort Level.zero) \
                 (Eq.refl (OptionType ImplExpr) (OptionType.some ImplExpr (ImplExpr.sort Level.zero))))"
            )),
            is_axiom: false,
            description: "FLAGSHIP non-vacuity witness: the identity lambda on Prop, \
                          lam(Prop, BVar 0) : Pi(Prop, Prop), derived in the empty context \
                          with next_id 0 -> 1. This is EXACTLY the acceptance \
                          KernelInferAccepts cannot represent — B's Lam arm recurses on the \
                          RAW de Bruijn body in the same state, so its lam inversion extracts \
                          KernelInferAccepts st (bvar 0) bt, which kernel_infer_bvar_empty \
                          makes Empty. Here the binder is OPENED to FVar(0) under an extended \
                          LCtx exactly as tc/infer.rs:533-548 does, the fvar rule infers the \
                          body, and impl_abstract_fvar rebuilds the Pi. Every step reduces: \
                          impl_open (bvar 0) 0 COMPUTES to fvar 0, and \
                          impl_abstract_fvar (sort 0) 0 COMPUTES to sort 0. Pure constructor \
                          application, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplWhnfTo".to_string(),
                "impl_open".to_string(),
                "impl_abstract_fvar".to_string(),
                "implinfer_sort_witness".to_string(),
                "lctx_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── pi ──────────────────────────────────────────────────────────────
        // Prop -> Prop : Sort (imax 1 1). Both sorts are whnf'd and required —
        // the Pi arm has NO infer_only guard (tc/infer.rs:550, it always checks).
        self.add_definition(SpecDefinition {
            name: "implinfer_pi_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.pi {BD} (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero)) \
                 (ImplExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero))) \
                 (Nat.succ Nat.zero)"
            ),
            value_src: Some(format!(
                "ImplInfer.pi {EMPTY_TENV} {NO_LPS} Nat.zero Nat.zero (Nat.succ Nat.zero) \
                 LCtx.nil {BD} (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero) \
                 (ImplExpr.sort (Level.succ Level.zero)) (ImplExpr.sort (Level.succ Level.zero)) \
                 (Level.succ Level.zero) (Level.succ Level.zero) \
                 implinfer_sort_witness \
                 (ImplWhnfTo.done (ImplExpr.sort (Level.succ Level.zero))) \
                 (ImplInfer.sort {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) {g1} Level.zero \
                 (Eq.refl Bool Bool.true)) \
                 (ImplWhnfTo.done (ImplExpr.sort (Level.succ Level.zero)))"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the pi rule: (Prop -> Prop) : \
                          Sort (imax 1 1), next_id 0 -> 1. Exercises the same fresh-id / open \
                          discipline as lam plus the SECOND ensure_sort on the codomain, and \
                          records that the Pi arm has no infer_only guard — it always checks \
                          (tc/infer.rs:550-583). The codomain here is closed, so \
                          impl_open (sort 0) 0 COMPUTES to sort 0. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplWhnfTo".to_string(),
                "implinfer_sort_witness".to_string(),
                "impl_open".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── app ─────────────────────────────────────────────────────────────
        // (λ(x : Type). x) Prop : Type. Exercises the whnf-to-Pi premise, the
        // is_le ascription check, and the instantiate of the codomain — the
        // three operations the release App arm performs. next_id 0 -> 1.
        let ident_ty = "(ImplExpr.lam (BinderData.mk BinderInfo.default Multiplicity.many) (ImplExpr.sort (Level.succ Level.zero)) (ImplExpr.bvar Nat.zero))";
        let g_ty = format!(
            "(LCtx.snoc LCtx.nil (LocalDecl.mk Nat.zero (ImplExpr.sort (Level.succ Level.zero)) \
             (OptionType.none ImplExpr) {BD}))"
        );
        let ident_ty_deriv = format!(
            "(ImplInfer.lam {EMPTY_TENV} {NO_LPS} Nat.zero Nat.zero (Nat.succ Nat.zero) \
             LCtx.nil {BD} (ImplExpr.sort (Level.succ Level.zero)) (ImplExpr.bvar Nat.zero) \
             (ImplExpr.sort (Level.succ (Level.succ Level.zero))) \
             (Level.succ (Level.succ Level.zero)) (ImplExpr.sort (Level.succ Level.zero)) \
             (ImplInfer.sort {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil (Level.succ Level.zero) \
             (Eq.refl Bool Bool.true)) \
             (ImplWhnfTo.done (ImplExpr.sort (Level.succ (Level.succ Level.zero)))) \
             (ImplInfer.fvar {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) {g_ty} Nat.zero \
             (ImplExpr.sort (Level.succ Level.zero)) \
             (Eq.refl (OptionType ImplExpr) \
             (OptionType.some ImplExpr (ImplExpr.sort (Level.succ Level.zero))))))"
        );
        self.add_definition(SpecDefinition {
            name: "implinfer_app_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.app {ident_ty} (ImplExpr.sort Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) (Nat.succ Nat.zero)"
            ),
            value_src: Some(format!(
                "ImplInfer.app {EMPTY_TENV} {NO_LPS} Nat.zero (Nat.succ Nat.zero) \
                 (Nat.succ Nat.zero) LCtx.nil {ident_ty} (ImplExpr.sort Level.zero) \
                 (ImplExpr.pi {BD} (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero))) \
                 {BD} (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) \
                 {ident_ty_deriv} \
                 (ImplWhnfTo.done (ImplExpr.pi {BD} (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)))) \
                 (ImplInfer.sort {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) LCtx.nil Level.zero \
                 (Eq.refl Bool Bool.true)) \
                 (ImplIsLe.refl (ImplExpr.sort (Level.succ Level.zero)))"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the app rule: (fun (x : Type) => x) Prop : \
                          Type. Exercises all three operations of the release App arm \
                          (tc/infer.rs:425-508) — whnf the function's type to a Pi, infer the \
                          argument, is_le the argument's type against the domain — and the \
                          instantiate of the codomain. next_id threads 0 -> 1 (function) -> 1 \
                          (argument), showing the counter is consumed left to right exactly as \
                          the arm evaluates. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplWhnfTo".to_string(),
                "ImplIsLe".to_string(),
                "impl_instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── let_ ────────────────────────────────────────────────────────────
        // let x : Type := Prop in x   :   Type
        // The context entry carries the VALUE (`some`) and the fixed
        // Default/Many binder data ctx_push_let stores; the result is
        // subst_fvar — zeta DIRECTLY, not instantiate.
        let g_let = format!(
            "(LCtx.snoc LCtx.nil (LocalDecl.mk Nat.zero (ImplExpr.sort (Level.succ Level.zero)) \
             (OptionType.some ImplExpr (ImplExpr.sort Level.zero)) {BD}))"
        );
        self.add_definition(SpecDefinition {
            name: "implinfer_let_witness".to_string(),
            type_src: format!(
                "ImplInfer {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil \
                 (ImplExpr.let_ Name.anonymous (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplExpr.sort Level.zero) (ImplExpr.bvar Nat.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) (Nat.succ Nat.zero)"
            ),
            value_src: Some(format!(
                "ImplInfer.let_ {EMPTY_TENV} {NO_LPS} Nat.zero Nat.zero Nat.zero \
                 (Nat.succ Nat.zero) LCtx.nil Name.anonymous \
                 (ImplExpr.sort (Level.succ Level.zero)) (ImplExpr.sort Level.zero) \
                 (ImplExpr.bvar Nat.zero) \
                 (ImplExpr.sort (Level.succ (Level.succ Level.zero))) \
                 (Level.succ (Level.succ Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplExpr.sort (Level.succ Level.zero)) \
                 (ImplInfer.sort {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil (Level.succ Level.zero) \
                 (Eq.refl Bool Bool.true)) \
                 (ImplWhnfTo.done (ImplExpr.sort (Level.succ (Level.succ Level.zero)))) \
                 (ImplInfer.sort {EMPTY_TENV} {NO_LPS} Nat.zero LCtx.nil Level.zero \
                 (Eq.refl Bool Bool.true)) \
                 (ImplIsLe.refl (ImplExpr.sort (Level.succ Level.zero))) \
                 (ImplInfer.fvar {EMPTY_TENV} {NO_LPS} (Nat.succ Nat.zero) {g_let} Nat.zero \
                 (ImplExpr.sort (Level.succ Level.zero)) \
                 (Eq.refl (OptionType ImplExpr) \
                 (OptionType.some ImplExpr (ImplExpr.sort (Level.succ Level.zero)))))"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for the let_ rule: \
                          `let x : Type := Prop in x` : Type, next_id 0 -> 1. Exercises the \
                          full check-mode Let path (tc/infer.rs:584-646): infer the \
                          annotation and whnf it to a sort, infer the value and is_le it \
                          against the annotation, then infer the body under a LET context \
                          entry that carries the VALUE (`some`) and the fixed \
                          Default/Many binder data ctx_push_let (tc/config.rs:48) stores through \
                          LocalContext::push_let (tc/local_context.rs:109-128). The result is impl_subst_fvar — ZETA \
                          DIRECTLY, not instantiate and not an abstract+instantiate round \
                          trip. KernelInferAccepts has no let arm at all. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplWhnfTo".to_string(),
                "ImplIsLe".to_string(),
                "impl_subst_fvar".to_string(),
                "impl_open".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

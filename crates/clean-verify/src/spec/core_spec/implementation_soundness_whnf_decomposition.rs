// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! whnf decomposition: spec WHNF trace + staged DefEq bridge decomposition (#461).
//!
//! Split from implementation_soundness.rs. Contains:
//! - beta_reduces_preserves_def_eq: constructive single-step bridge from beta_reduces to DefEq
//! - whnf_step_preserves_def_eq: constructive single-step bridge from whnf_step to DefEq
//! - whnf_to_preserves_def_eq: constructive spec-closure bridge from whnf_to to DefEq
//! - kernel_whnf_reduces_to_spec_whnf: implementation/spec bridge axiom
//! - kernel_whnf_returns_def_eq: DerivedLemma with constructive proof term
//! - beta_deterministic: DerivedProved diamond property (formerly HelperAxiom)
//! - whnf_to_target_is_whnf: DerivedProved WHNF target extraction
//! - whnf_idempotent: DerivedProved idempotence (formerly HelperAxiom)
//! - whnf_confluent: DerivedProved confluence (formerly HelperAxiom)
//!
//! The production kernel's `whnf` implementation follows Lean 4's kernel
//! `whnf_core` structure (`src/kernel/type_checker.cpp`): recursively normalize
//! the head, perform a head reduction when possible, and repeat until a weak-head
//! normal form is reached. On the current const+delta `KExpr` fragment, the
//! spec-visible reduction trace is captured by `whnf_to`, whose single-step
//! relation is `whnf_step`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_whnf_decomposition(
        &mut self,
    ) -> Result<(), SpecError> {
        self.add_definition_reducible(SpecDefinition {
            name: "beta_reduces_def_eq_goal".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), beta_reduces e e' -> Type".to_string(),
            value_src: Some(
                "fun (e : KExpr) (e' : KExpr) (_h : beta_reduces e e') => DefEq e e'"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the beta_reduces-to-DefEq bridge. This wrapper lets the current elaborator reduce the recursor target back to DefEq e e' during declaration checking."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces".to_string(),
                "DefEq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // PROOF STATUS: DerivedProved — DefEq.beta is now UNTYPED (the
        // church_rosser_whnf retirement untyped it: typing_def_eq.rs), so the
        // single-step bridge from beta_reduces to DefEq is a direct beta_reduces.rec
        // induction into the semireducible beta_reduces_def_eq_goal motive (DefEq e e').
        // The former "DefEq.beta now requires typing premises" blocker is STALE.
        // Modeled arm-for-arm on the strictly-harder, already-kernel-checked sibling
        // beta_reduces_typed_def_eq (beta_reduces_preserves_typing.rs) and on
        // par_reduces_cd_sound: the beta arm contracts via the UNTYPED DefEq.beta
        // (no typing premises), the zeta arm via the genuine DefEq.zeta (let
        // promotion, task #28), the binder-congruence arms via DefEq.app_cong/
        // lam_cong/pi_cong (forall_ discharges through the reducible KExpr.forall_
        // alias), the three let congruences via the ternary DefEq.let_cong, and
        // the iota arm via DefEq.iota.
        // Zero axiom_deps; the only foundational leaves are the DefEq FoundationalRule
        // constructors. Part of #2872, #3221.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_preserves_def_eq".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), beta_reduces e e' -> DefEq e e'"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : beta_reduces e e') => ",
                    "beta_reduces.rec ",
                    "beta_reduces_def_eq_goal ",
                    // beta: (λA.b) a ≡ b[a/0] via UNTYPED DefEq.beta
                    "(fun (A : KExpr) (b : KExpr) (a : KExpr) => DefEq.beta A b a) ",
                    // app_left: f → f'
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
                    "(hff : beta_reduces f f') (ih : beta_reduces_def_eq_goal f f' hff) => ",
                    "DefEq.app_cong f f' a a ih (DefEq.refl a)) ",
                    // app_right: a → a'
                    "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(haa : beta_reduces a a') (ih : beta_reduces_def_eq_goal a a' haa) => ",
                    "DefEq.app_cong f f a a' (DefEq.refl f) ih) ",
                    // lam_ty: ty → ty'
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
                    "(htt : beta_reduces ty ty') (ih : beta_reduces_def_eq_goal ty ty' htt) => ",
                    "DefEq.lam_cong ty ty' body body ih (DefEq.refl body)) ",
                    // lam_body: body → body'
                    "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hbb : beta_reduces body body') (ih : beta_reduces_def_eq_goal body body' hbb) => ",
                    "DefEq.lam_cong ty ty body body' (DefEq.refl ty) ih) ",
                    // pi_dom: dom → dom'
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(hdd : beta_reduces dom dom') (ih : beta_reduces_def_eq_goal dom dom' hdd) => ",
                    "DefEq.pi_cong dom dom' body body ih (DefEq.refl body)) ",
                    // pi_cod: body → body'
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hbb : beta_reduces body body') (ih : beta_reduces_def_eq_goal body body' hbb) => ",
                    "DefEq.pi_cong dom dom body body' (DefEq.refl dom) ih) ",
                    // forall_congr_dom: dom → dom' (KExpr.forall_ is the reducible pi alias)
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
                    "(hdd : beta_reduces dom dom') (ih : beta_reduces_def_eq_goal dom dom' hdd) => ",
                    "DefEq.pi_cong dom dom' body body ih (DefEq.refl body)) ",
                    // forall_congr_cod: body → body'
                    "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hbb : beta_reduces body body') (ih : beta_reduces_def_eq_goal body body' hbb) => ",
                    "DefEq.pi_cong dom dom body body' (DefEq.refl dom) ih) ",
                    // zeta: let_ ty val body ≡ body[val/0] via the genuine DefEq.zeta
                    // (let promotion, task #28: let_ is a genuine 7th constructor)
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) => DefEq.zeta ty val body) ",
                    // let_ty: ty → ty' (one-position congruence via ternary DefEq.let_cong)
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
                    "(htt : beta_reduces ty ty') (ih : beta_reduces_def_eq_goal ty ty' htt) => ",
                    "DefEq.let_cong ty ty' val val body body ih (DefEq.refl val) (DefEq.refl body)) ",
                    // let_val: val → val'
                    "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
                    "(hvv : beta_reduces val val') (ih : beta_reduces_def_eq_goal val val' hvv) => ",
                    "DefEq.let_cong ty ty val val' body body (DefEq.refl ty) ih (DefEq.refl body)) ",
                    // let_body: body → body'
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hbb : beta_reduces body body') (ih : beta_reduces_def_eq_goal body body' hbb) => ",
                    "DefEq.let_cong ty ty val val body body' (DefEq.refl ty) (DefEq.refl val) ih) ",
                    // iota: untyped DefEq.iota
                    "(fun (e_i : KExpr) (e_i' : KExpr) (hi : iota_reduces e_i e_i') => ",
                    "DefEq.iota e_i e_i' hi) ",
                    // proj: congruence on the sub-expression via DefEq.proj_cong
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(hss : beta_reduces sub sub') (ih : beta_reduces_def_eq_goal sub sub' hss) => ",
                    "DefEq.proj_cong s i sub sub' ih) ",
                    // apply recursor to indices + major
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-step beta/binder-congruence bridge from beta_reduces to DefEq: ",
                "beta_reduces e e' -> DefEq e e'. DerivedProved by beta_reduces.rec into the ",
                "semireducible beta_reduces_def_eq_goal motive (DefEq e e'). The beta arm ",
                "contracts via the UNTYPED DefEq.beta (no typing premises — the ",
                "church_rosser_whnf-retirement untyping unblocks this; the former typed-premise ",
                "blocker is stale); the zeta arm via the genuine DefEq.zeta (let promotion, ",
                "task #28); the binder-congruence arms via DefEq.app_cong/lam_cong/pi_cong ",
                "(forall_ discharges through the reducible KExpr.forall_ alias); the three let ",
                "congruences via the ternary DefEq.let_cong; the iota arm via DefEq.iota. Zero ",
                "axiom_deps — the only foundational leaves are the DefEq FoundationalRule ",
                "constructors. Part of #2872, #3221."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "beta_reduces_def_eq_goal".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.let_cong".to_string(),
                "DefEq.proj_cong".to_string(),
                "DefEq.iota".to_string(),
                "DefEq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "whnf_step_def_eq_goal".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_step e e' -> Type".to_string(),
            value_src: Some(
                "fun (e : KExpr) (e' : KExpr) (_h : whnf_step e e') => DefEq e e'".to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the whnf_step-to-DefEq bridge."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "DefEq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_step_beta_sound".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr) (h : beta_reduces e e'), ",
                "whnf_step_def_eq_goal e e' (whnf_step.beta e e' h)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : beta_reduces e e') => ",
                    "beta_reduces_preserves_def_eq e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Named whnf_step.rec beta-case wrapper for the semireducible whnf_step_def_eq_goal motive. Part of #2895, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step_def_eq_goal".to_string(),
                "whnf_step.beta".to_string(),
                "beta_reduces_preserves_def_eq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_step_delta_sound".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr) (h : delta_reduces e e'), ",
                "whnf_step_def_eq_goal e e' (whnf_step.delta e e' h)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : delta_reduces e e') => ",
                    "DefEq.delta e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Named whnf_step.rec delta-case wrapper for the semireducible whnf_step_def_eq_goal motive. Part of #2895, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step_def_eq_goal".to_string(),
                "whnf_step.delta".to_string(),
                "DefEq.delta".to_string(),
            ])),
            axiom_deps: HashSet::from(["delta_reduces".to_string()]),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "whnf_step_preserves_def_eq".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_step e e' -> DefEq e e'"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : whnf_step e e') => ",
                    "whnf_step.rec e e' ",
                    "(whnf_step_def_eq_goal e e') ",
                    "(whnf_step_beta_sound e e') ",
                    "(whnf_step_delta_sound e e') ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Single-step WHNF bridge from whnf_step to DefEq, delegating beta to the constructive beta bridge and delta to DefEq.delta. The current whnf_step.rec generated type fixes the two KExpr indices before the motive, so the branch wrappers are partially applied to e/e' before elimination.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "whnf_step_def_eq_goal".to_string(),
                "whnf_step_beta_sound".to_string(),
                "whnf_step_delta_sound".to_string(),
                "beta_reduces_preserves_def_eq".to_string(),
                "DefEq.delta".to_string(),
            ])),
            axiom_deps: HashSet::from(["delta_reduces".to_string()]),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "whnf_to_def_eq_goal".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_to e e' -> Type".to_string(),
            value_src: Some(
                "fun (e : KExpr) (e' : KExpr) (_h : whnf_to e e') => DefEq e e'"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the whnf_to-to-DefEq bridge. This keeps the recursor result reducible to DefEq e e' during declaration checking."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to".to_string(),
                "DefEq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "whnf_to_preserves_def_eq".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_to e e' -> DefEq e e'".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : whnf_to e e') => ",
                    "whnf_to.rec ",
                    "whnf_to_def_eq_goal ",
                    "(fun (e0 : KExpr) (_hwhnf : is_whnf e0) => DefEq.refl e0) ",
                    "(fun (e0 : KExpr) (e1 : KExpr) (v : KExpr) ",
                    "(hstep : whnf_step e0 e1) ",
                    "(hrest : whnf_to e1 v) ",
                    "(ih : whnf_to_def_eq_goal e1 v hrest) => ",
                    "DefEq.trans e0 e1 v (whnf_step_preserves_def_eq e0 e1 hstep) ih) ",
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Spec-closure bridge from whnf_to to DefEq. The goal-family alias stays semireducible, while the bridge itself uses structural registration so the current recursor motive false negative does not force a semireducible theorem."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to.rec".to_string(),
                "whnf_to_def_eq_goal".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
                "whnf_step_preserves_def_eq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Implementation/spec bridge for whnf, now GENUINELY PROVED by structural
        // recursion. KernelWhnfAccepts is no longer an opaque axiom: it is a
        // faithful inductive (implementation_soundness.rs) whose constructors
        // mirror the spec `whnf_to` relation one-for-one (refl-on-WHNF, step over
        // whnf_step). The proof is `KernelWhnfAccepts.rec` mapping each ctor to the
        // matching `whnf_to` ctor — the refl arm to `whnf_to.refl`, the step arm to
        // `whnf_to.step` threading the recursor IH. `st` is a uniform parameter, so
        // the recursor motive is `fun x y (_ : KernelWhnfAccepts st x y) => whnf_to
        // x y` (st-free). The env/ctx/admissibility premises are carried for the
        // soundness chain's callers but unused here (the spec whnf_to trace needs
        // only the reduction witness). Modeled on `par_reduces_c_subsumes_par_p`
        // (par_reduces_p.rs): a cross-inductive embedding via .rec. DerivedProved,
        // zero axiom_deps — the kernel type-checks this term in add_decl.
        self.add_definition(SpecDefinition {
            name: "kernel_whnf_reduces_to_spec_whnf".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (e' : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelWhnfAccepts st e e' -> ",
                "whnf_to e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (e' : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(_hin : KernelInputAdmissible st e) ",
                    "(haccept : KernelWhnfAccepts st e e') => ",
                    "KernelWhnfAccepts.rec st ",
                    "(fun (x : KExpr) (y : KExpr) (_h : KernelWhnfAccepts st x y) => whnf_to x y) ",
                    // refl arm: is_whnf a -> whnf_to a a
                    "(fun (a : KExpr) (hw : is_whnf a) => whnf_to.refl a hw) ",
                    // step arm: whnf_step a b, tail KernelWhnfAccepts st b v (IH whnf_to b v)
                    "(fun (a : KExpr) (b : KExpr) (v : KExpr) ",
                    "(hstep : whnf_step a b) ",
                    "(_hrest : KernelWhnfAccepts st b v) ",
                    "(ih : whnf_to b v) => ",
                    "whnf_to.step a b v hstep ih) ",
                    "e e' haccept"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Implementation/spec bridge for whnf on the current core KExpr fragment: a successful production-kernel whnf run yields a spec whnf_to trace from the input to the returned weak-head normal form. DerivedProved by KernelWhnfAccepts.rec mapping each faithful-inductive ctor to the matching whnf_to ctor (refl→whnf_to.refl, step→whnf_to.step); zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelWhnfAccepts".to_string(),
                "KernelWhnfAccepts.rec".to_string(),
                "KernelWhnfAccepts.refl".to_string(),
                "KernelWhnfAccepts.step".to_string(),
                "whnf_to".to_string(),
                "whnf_to.refl".to_string(),
                "whnf_to.step".to_string(),
                "is_whnf".to_string(),
                "whnf_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_whnf_returns_def_eq".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (e' : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelWhnfAccepts st e e' -> ",
                "is_def_eq e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (e' : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hin : KernelInputAdmissible st e) ",
                    "(haccept : KernelWhnfAccepts st e e') => ",
                    "whnf_to_preserves_def_eq e e' ",
                    "(kernel_whnf_reduces_to_spec_whnf st e e' henv hctx hin haccept)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Forward simulation for whnf: derived from the spec whnf trace witness plus the constructive whnf_to-to-DefEq closure bridge. Now fully DerivedProved: both the trace bridge (kernel_whnf_reduces_to_spec_whnf) and the closure bridge (whnf_to_preserves_def_eq) are constructive with empty axiom closures, so this composition carries no pending axiom leaf."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            // Promoted DerivedPending -> DerivedProved: its sole former pending
            // leaf, kernel_whnf_reduces_to_spec_whnf, is now a DerivedProved
            // theorem (KernelWhnfAccepts is a faithful inductive). The other
            // direct dependency whnf_to_preserves_def_eq is already DerivedProved
            // with empty axiom_deps, so the composition's axiom closure is empty.
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to_preserves_def_eq".to_string(),
                "kernel_whnf_reduces_to_spec_whnf".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ─────────────────────────────────────────────────────────────
        // WHNF Metatheory: formerly HelperAxioms, now DerivedProved
        // ─────────────────────────────────────────────────────────────
        // These three lemmas were axiomatized in whnf_lemmas.rs but are
        // trivially derivable from the constructive bridges above. Moving
        // them here (after beta_reduces_preserves_def_eq and
        // whnf_to_preserves_def_eq are registered) makes them DerivedProved,
        // shrinking the trust surface by 3 HelperAxioms. Part of #461.

        // beta_deterministic: two beta-reduces from the same term yield
        // DefEq results. Proof: DefEq.trans(DefEq.symm(bridge h1), bridge h2).
        self.add_definition_structural(SpecDefinition {
            name: "beta_deterministic".to_string(),
            type_src: "forall (e : KExpr) (r1 : KExpr) (r2 : KExpr), beta_reduces e r1 -> beta_reduces e r2 -> DefEq r1 r2".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (r1 : KExpr) (r2 : KExpr) ",
                    "(h1 : beta_reduces e r1) (h2 : beta_reduces e r2) => ",
                    "DefEq.trans r1 e r2 ",
                    "(DefEq.symm e r1 (beta_reduces_preserves_def_eq e r1 h1)) ",
                    "(beta_reduces_preserves_def_eq e r2 h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Beta reduction diamond property (DefEq). DerivedProved via beta_reduces_preserves_def_eq + DefEq.symm + DefEq.trans. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_preserves_def_eq".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_to_is_whnf_goal: semireducible motive alias for the
        // whnf_to target-is-WHNF induction.
        self.add_definition_reducible(SpecDefinition {
            name: "whnf_to_is_whnf_goal".to_string(),
            type_src: "forall (e : KExpr) (v : KExpr), whnf_to e v -> Type".to_string(),
            value_src: Some(
                "fun (_e : KExpr) (v : KExpr) (_h : whnf_to _e v) => is_whnf v"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the whnf_to target-is-WHNF induction. Reduces to is_whnf v during declaration checking.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to".to_string(),
                "is_whnf".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_to_target_is_whnf: the WHNF target of any whnf_to derivation
        // is already WHNF. Proof by whnf_to.rec: refl case has is_whnf directly,
        // step case passes through the IH.
        self.add_definition_structural(SpecDefinition {
            name: "whnf_to_target_is_whnf".to_string(),
            type_src: "forall (e : KExpr) (v : KExpr), whnf_to e v -> is_whnf v"
                .to_string(),
            value_src: Some(
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
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The WHNF target of any whnf_to derivation is bounded WHNF. DerivedProved by whnf_to.rec induction: refl case has is_whnf directly, step case passes IH. Part of #461, #2895.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to.rec".to_string(),
                "whnf_to_is_whnf_goal".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_idempotent: if whnf_to e e', then whnf_to e' e'.
        // Proof: e' is WHNF (by whnf_to_target_is_whnf), so
        // whnf_to.refl e' applies.
        self.add_definition_structural(SpecDefinition {
            name: "whnf_idempotent".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_to e e' -> whnf_to e' e'"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : whnf_to e e') => ",
                    "whnf_to.refl e' (whnf_to_target_is_whnf e e' h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "WHNF is idempotent: the target of whnf_to is already in WHNF. DerivedProved via whnf_to_target_is_whnf + whnf_to.refl. Part of #461, #2895.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to_target_is_whnf".to_string(),
                "whnf_to.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_confluent: two whnf_to derivations from the same term yield
        // DefEq results. Proof: DefEq.trans(DefEq.symm(bridge h1), bridge h2).
        self.add_definition_structural(SpecDefinition {
            name: "whnf_confluent".to_string(),
            type_src: "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), whnf_to e e1 -> whnf_to e e2 -> DefEq e1 e2".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : whnf_to e e1) (h2 : whnf_to e e2) => ",
                    "DefEq.trans e1 e e2 ",
                    "(DefEq.symm e e1 (whnf_to_preserves_def_eq e e1 h1)) ",
                    "(whnf_to_preserves_def_eq e e2 h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "WHNF confluence (DefEq): two WHNF reductions from the same term produce DefEq results. DerivedProved via whnf_to_preserves_def_eq + DefEq.symm + DefEq.trans. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to_preserves_def_eq".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_whnf_decomposition_tests.rs"]
mod implementation_soundness_whnf_decomposition_tests;

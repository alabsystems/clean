// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! High-level algorithmic type-checker contracts for #462.
//!
//! This module adds a thin specification surface for the production checker's
//! public entry points:
//! - `infer_type` correctness over the summary state bridge
//! - `is_def_eq` reflexivity and symmetry
//! - `whnf` idempotency
//!
//! The deep implementation-soundness decomposition already lives in
//! `core_spec`. These definitions expose the intended algorithmic contracts as
//! named specification items without changing the existing bundle planner.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_tc_spec(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "tc_infer_type_correct".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelStateMatchesSpec st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelInferAccepts st e T -> ",
                "has_type e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(hstate : KernelStateMatchesSpec st) ",
                    "(hadm : KernelInputAdmissible st e) ",
                    "(hinfer : KernelInferAccepts st e T) => ",
                    "KernelInferSound_summary st e T hstate hadm hinfer"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Algorithmic infer_type correctness contract: in a kernel state matching the specification, every accepted inference result witnesses the spec typing judgment for the input expression. This surfaces the infer_type ENSURES clause from clean-kernel on top of the summary state bridge. Part of #462.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferSound_summary".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelInferAccepts".to_string(),
                "has_type".to_string(),
            ])),
            // The six per-case infer axioms (and the opaque KernelInferAccepts
            // token) are no longer axiom leaves — KernelInferAccepts is a
            // faithful inductive (Step 3) and all six per-case lemmas are
            // derived from it via kernel_infer_inversion. The residual is the
            // master inversion's closure (10 infer-band skolems +
            // KernelCheckAccepts) plus the check/defeq band.
            axiom_deps: HashSet::from([
                "kernel_infer_returns_well_typed".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "tc_is_def_eq_reflexive".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr), ",
                "KernelStateMatchesSpec st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelDefEqAccepts st e e"
            )
            .to_string(),
            // DERIVED (was a HelperAxiom): after the def-eq un-Skolemization,
            // KernelDefEqAccepts.mk carries `guards -> DefEqJoinable a b`, and
            // DefEqJoinable e e is trivially constructible (nl=nr=e, three
            // DefEq.refl) — so is_def_eq reflexivity is PROVED, not assumed. The
            // guards are discharged vacuously (the refl witness needs none).
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) ",
                    "(hmatch : KernelStateMatchesSpec st) ",
                    "(hadm : KernelInputAdmissible st e) => ",
                    "KernelDefEqAccepts.mk st e e ",
                    "(fun (h1 : KernelStateEnvValid st) ",
                    "(h2 : KernelStateLocalCtxWellFormed st) ",
                    "(h3 : KernelBinaryInputAdmissible st e e) => ",
                    "DefEqJoinable.mk e e e e ",
                    "(DefEq.refl e) (DefEq.refl e) (DefEq.refl e))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "is_def_eq reflexivity, DERIVED from the DefEqJoinable inductive (KernelDefEqAccepts.mk st e e via DefEqJoinable e e = three DefEq.refl). Formerly a HelperAxiom; now DerivedProved, zero axiom_deps. Downstream payoff of the def-eq skolem un-Skolemization. Part of #462.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelDefEqAccepts".to_string(),
                "DefEqJoinable".to_string(),
                "DefEq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "tc_is_def_eq_symmetric".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (a : KExpr) (b : KExpr), ",
                "KernelStateMatchesSpec st -> ",
                "KernelBinaryInputAdmissible st a b -> ",
                "KernelDefEqAccepts st a b -> ",
                "KernelDefEqAccepts st b a"
            )
            .to_string(),
            // DERIVED (was a HelperAxiom): eliminate the input via
            // KernelDefEqAccepts.rec (discharging the field's guards with the kept
            // henv/hctx and the lemma's OWN KernelBinaryInputAdmissible st a b
            // hypothesis) to get DefEqJoinable a b; swap it (nl<->nr, DefEq.symm on
            // the middle) to DefEqJoinable b a; rebuild via KernelDefEqAccepts.mk
            // st b a. Symmetry is PROVED, not assumed — the def-eq un-Skolemization
            // downstream payoff.
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (a : KExpr) (b : KExpr) ",
                    "(hmatch : KernelStateMatchesSpec st) ",
                    "(hadm : KernelBinaryInputAdmissible st a b) ",
                    "(h : KernelDefEqAccepts st a b) => ",
                    "KernelDefEqAccepts.mk st b a ",
                    "(fun (henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm_ba : KernelBinaryInputAdmissible st b a) => ",
                    "DefEqJoinable.rec a b ",
                    "(fun (_j : DefEqJoinable a b) => DefEqJoinable b a) ",
                    "(fun (nl : KExpr) (nr : KExpr) ",
                    "(h1 : DefEq a nl) (h2 : DefEq b nr) (h3 : DefEq nl nr) => ",
                    "DefEqJoinable.mk b a nr nl h2 h1 (DefEq.symm nl nr h3)) ",
                    "(KernelDefEqAccepts.rec st a b ",
                    "(fun (_k : KernelDefEqAccepts st a b) => DefEqJoinable a b) ",
                    "(fun (field : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelBinaryInputAdmissible st a b -> DefEqJoinable a b) => ",
                    "field henv hctx hadm) ",
                    "h))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "is_def_eq symmetry, DERIVED: KernelDefEqAccepts.rec gives DefEqJoinable a b (guards discharged via the lemma's own admissibility hypothesis), swapped to DefEqJoinable b a and rebuilt via .mk. Formerly a HelperAxiom; now DerivedProved, zero axiom_deps. Downstream payoff of the def-eq skolem un-Skolemization. Part of #462.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelBinaryInputAdmissible".to_string(),
                "KernelDefEqAccepts".to_string(),
                "DefEqJoinable".to_string(),
                "DefEq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "tc_whnf_idempotent".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (v : KExpr), ",
                "KernelStateMatchesSpec st -> ",
                "KernelInputAdmissible st e -> ",
                "KernelWhnfAccepts st e v -> ",
                "KernelWhnfAccepts st v v"
            )
            .to_string(),
            // PROVED by structural recursion over the KernelWhnfAccepts witness.
            // KernelWhnfAccepts is no longer an opaque axiom — it is a faithful
            // inductive (implementation_soundness.rs) with a refl ctor on a term
            // already in WHNF and a step ctor over a single whnf_step. The result
            // of any whnf run is therefore in WHNF: in the refl arm the witness
            // already carries `is_whnf a`, so `KernelWhnfAccepts.refl st a hwa`
            // rebuilds the goal at the returned value; in the step arm the IH at
            // the tail already establishes `KernelWhnfAccepts st w w` for the final
            // value `w`. `st` is a uniform parameter, so the recursor motive
            // `fun x y _ => KernelWhnfAccepts st y y` is st-free. The state /
            // admissibility premises are carried for the soundness chain's callers
            // but unused here. Modeled on `kernel_whnf_reduces_to_spec_whnf`
            // (implementation_soundness_whnf_decomposition.rs). DerivedProved, zero
            // axiom_deps — the kernel type-checks this term in add_decl.
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (v : KExpr) ",
                    "(_hstate : KernelStateMatchesSpec st) ",
                    "(_hadm : KernelInputAdmissible st e) ",
                    "(haccept : KernelWhnfAccepts st e v) => ",
                    "KernelWhnfAccepts.rec st ",
                    "(fun (x : KExpr) (y : KExpr) (_h : KernelWhnfAccepts st x y) => ",
                    "KernelWhnfAccepts st y y) ",
                    "(fun (a : KExpr) (hwa : is_whnf a) => KernelWhnfAccepts.refl st a hwa) ",
                    "(fun (a : KExpr) (b : KExpr) (w : KExpr) ",
                    "(hstep : whnf_step a b) ",
                    "(_hrest : KernelWhnfAccepts st b w) ",
                    "(ih : KernelWhnfAccepts st w w) => ih) ",
                    "e v haccept"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Algorithmic whnf idempotency contract: once the checker reduces an admissible expression to weak-head normal form, running whnf again returns the same result. This names the public TypeChecker::whnf idempotency guarantee in the specification. PROVED by KernelWhnfAccepts.rec: the refl arm reuses the witness's is_whnf evidence, the step arm reuses the tail IH; the result of a whnf run is always in WHNF. Part of #462.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelWhnfAccepts".to_string(),
                "KernelWhnfAccepts.rec".to_string(),
                "KernelWhnfAccepts.refl".to_string(),
                "is_whnf".to_string(),
                "whnf_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

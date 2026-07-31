// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Sort/bvar infer_type refinement foundations (#461).
//!
//! This root module contains only the sort exact-result bridge and bvar
//! closedness inversion. The remaining per-case bridges live in split modules:
//!
//! - `implementation_soundness_infer_refinement_app.rs`: app-case local bridge
//! - `implementation_soundness_infer_refinement_binder.rs`: lam/pi binder witnesses (#2869)
//! - `implementation_soundness_infer_refinement_dispatch.rs`: KExpr.rec dispatcher

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// Inline KExpr.rec discriminator: non-BVar -> Nat, BVar -> Empty.
/// (let_ minor returns Nat — a let is not a BVar.)
const KEXPR_NOT_BVAR_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // Foundation: Lt n 0 → Empty (constructive)
        // =========================================================
        //
        // Both constructors of Lt produce Lt _ (Nat.succ _):
        //   - Lt.zero_lt_succ n : Lt 0 (succ n)
        //   - Lt.succ_lt_succ n m h : Lt (succ n) (succ m)
        // So Lt n 0 is uninhabited — proved via Lt.rec with a motive
        // that returns Empty when b = 0 and Nat when b = succ _.
        //
        // Proof: Nat.rec on the second Lt index b. At b = 0 the motive
        // is Empty; at b = succ _ it is Nat. Both Lt constructors target
        // succ indices, so each case produces Nat.zero. Applying Lt.rec
        // to h : Lt n 0 yields the Empty type.

        self.add_definition_reducible(SpecDefinition {
            name: "not_lt_zero_goal".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a b -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (_ : Lt a b) => ",
                    "Nat.rec (fun (_ : Nat) => Type) Empty ",
                    "(fun (_ : Nat) (_ : Type) => Nat) b"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible motive alias for the Lt-to-Empty elimination. ",
                "Reduces to Empty at b = 0 and Nat at b = succ _. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.rec".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "not_lt_zero".to_string(),
            type_src: "forall (n : Nat), Lt n Nat.zero -> Empty".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (h : Lt n Nat.zero) => ",
                    "Lt.rec ",
                    "not_lt_zero_goal ",
                    "(fun (k : Nat) => Nat.zero) ",
                    "(fun (k : Nat) (m : Nat) (hltkm : Lt k m) ",
                    "(_ih : not_lt_zero_goal k m hltkm) => Nat.zero) ",
                    "n Nat.zero h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "No natural number is less than zero. Constructive proof via Lt.rec ",
                "with large elimination: both Lt constructors (zero_lt_succ, succ_lt_succ) ",
                "produce Lt _ (Nat.succ _), so the motive evaluates to Nat for each case ",
                "(trivially satisfied by Nat.zero). At the target Lt n 0 the motive evaluates ",
                "to Empty, completing the proof. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt.rec".to_string(),
                "not_lt_zero_goal".to_string(),
                "Nat.zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // BVar closedness inversion
        // =========================================================
        //
        // is_closed (KExpr.bvar n) = is_closed_at (KExpr.bvar n) 0.
        // The only constructor for is_closed_at on bvar is:
        //   is_closed_at.bvar i d (h : Lt i d)
        // At d = 0, this requires Lt n 0, which is impossible (not_lt_zero).
        //
        // Constructive proof uses is_closed_at.rec with an equality-indexed
        // motive, matching the app/lam/pi admissibility inversions. The
        // impossible non-bvar cases discharge via KExpr discrimination, and
        // the matching bvar case transports the Lt witness across the
        // constructor equality with Eq.subst. Part of #461.

        self.add_definition(SpecDefinition {
            name: "is_closed_at_bvar_inv".to_string(),
            type_src: "forall (i : Nat) (d : Nat), is_closed_at (KExpr.bvar i) d -> Lt i d"
                .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (i : Nat) (d : Nat) (h : is_closed_at (KExpr.bvar i) d) => ",
                    "is_closed_at.rec ",
                    "(fun (e : KExpr) (depth : Nat) (_hc : is_closed_at e depth) => ",
                    "Eq KExpr e (KExpr.bvar i) -> Lt i depth) ",
                    "(fun (n : Level) (depth : Nat) ",
                    "(eq : Eq KExpr (KExpr.sort n) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.sort n) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (j : Nat) (depth : Nat) (hlt : Lt j depth) ",
                    "(eq : Eq KExpr (KExpr.bvar j) (KExpr.bvar i)) => ",
                    "Eq.substType KExpr ",
                    "(KExpr.rec (fun (_ : KExpr) => Type) ",
                    "(fun (_ : Level) => Nat) ",
                    "(fun (k : Nat) => Lt k depth) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
                    "(fun (_ : Nat) => Nat)) ",
                    "(KExpr.bvar j) (KExpr.bvar i) eq hlt) ",
                    "(fun (f : KExpr) (a : KExpr) (depth : Nat) ",
                    "(_hf : is_closed_at f depth) (_ha : is_closed_at a depth) ",
                    "(_ihf : Eq KExpr f (KExpr.bvar i) -> Lt i depth) ",
                    "(_iha : Eq KExpr a (KExpr.bvar i) -> Lt i depth) ",
                    "(eq : Eq KExpr (KExpr.app f a) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.app f a) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (A : KExpr) (body : KExpr) (depth : Nat) ",
                    "(_hA : is_closed_at A depth) (_hbody : is_closed_at body (Nat.succ depth)) ",
                    "(_ihA : Eq KExpr A (KExpr.bvar i) -> Lt i depth) ",
                    "(_ihbody : Eq KExpr body (KExpr.bvar i) -> Lt i (Nat.succ depth)) ",
                    "(eq : Eq KExpr (KExpr.lam A body) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.lam A body) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (A : KExpr) (body : KExpr) (depth : Nat) ",
                    "(_hA : is_closed_at A depth) (_hbody : is_closed_at body (Nat.succ depth)) ",
                    "(_ihA : Eq KExpr A (KExpr.bvar i) -> Lt i depth) ",
                    "(_ihbody : Eq KExpr body (KExpr.bvar i) -> Lt i (Nat.succ depth)) ",
                    "(eq : Eq KExpr (KExpr.pi A body) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.pi A body) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (n : Name) (us : ListType Level) (depth : Nat) ",
                    "(eq : Eq KExpr (KExpr.const n us) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.const n us) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (depth : Nat) ",
                    "(_hty : is_closed_at ty depth) (_hval : is_closed_at val depth) ",
                    "(_hbody : is_closed_at body (Nat.succ depth)) ",
                    "(_ihty : Eq KExpr ty (KExpr.bvar i) -> Lt i depth) ",
                    "(_ihval : Eq KExpr val (KExpr.bvar i) -> Lt i depth) ",
                    "(_ihbody : Eq KExpr body (KExpr.bvar i) -> Lt i (Nat.succ depth)) ",
                    "(eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.let_ ty val body) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (s : Name) (i0 : Nat) (sub : KExpr) (depth : Nat) ",
                    "(_hsub : is_closed_at sub depth) ",
                    "(_ihsub : Eq KExpr sub (KExpr.bvar i) -> Lt i depth) ",
                    "(eq : Eq KExpr (KExpr.proj s i0 sub) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.proj s i0 sub) (KExpr.bvar i) eq Nat.zero)) ",
                    "(fun (v : Nat) (depth : Nat) ",
                    "(eq : Eq KExpr (KExpr.lit v) (KExpr.bvar i)) => ",
                    "Empty.rec (fun (_ : Empty) => Lt i depth) ",
                    "(Eq.substType KExpr {not_bvar} ",
                    "(KExpr.lit v) (KExpr.bvar i) eq Nat.zero)) ",
                    "(KExpr.bvar i) d h (Eq.refl KExpr (KExpr.bvar i))"
                ),
                not_bvar = KEXPR_NOT_BVAR_INLINE
            )),
            is_axiom: false,
            description: concat!(
                "Inversion of is_closed_at on bvar: the only constructor matching ",
                "is_closed_at (KExpr.bvar i) d is is_closed_at.bvar i d (h : Lt i d), ",
                "so we recover Lt i d. DerivedProved via is_closed_at.rec with ",
                "constructor equality indexing: impossible non-bvar cases are ",
                "discharged by KExpr discrimination, and the matching bvar case ",
                "transports the Lt witness across Eq.subst. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_closed_at".to_string(),
                "Lt".to_string(),
                "is_closed_at.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "bvar_not_closed".to_string(),
            type_src: "forall (n : Nat), is_closed (KExpr.bvar n) -> Empty".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (h : is_closed (KExpr.bvar n)) => ",
                    "not_lt_zero n (is_closed_at_bvar_inv n Nat.zero h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Bound variables are never closed: is_closed (bvar n) is uninhabited. ",
                "Proof: invert is_closed_at to get Lt n 0, then apply not_lt_zero. ",
                "Fully constructive now that both is_closed_at_bvar_inv and ",
                "not_lt_zero are DerivedProved. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "not_lt_zero".to_string(),
                "is_closed_at_bvar_inv".to_string(),
                "is_closed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Per-case forward simulation axioms
        // =========================================================
        //
        // Each axiom maps a specific case of infer_type_fast_inner
        // (clean-kernel/src/tc/infer.rs) to the corresponding Typing rule.
        //
        // Sort case: kernel returns sort(succ(l)) for sort(l) input.
        // Exact-result axiom + constructive correspondence via Typing.sort.

        // kernel_infer_const_sound: formerly a HelperAxiom, now DERIVED from the
        // faithful KernelInferAccepts inductive: the const constructor's single
        // field IS this guarded implication verbatim, and the master inversion
        // recovers it. The guard premises henv/hctx/hadm are GENUINELY CONSUMED
        // (applied to the recovered implication) — the old axiom's guarded
        // strength preserved exactly (Step-2 pin pattern).
        self.add_definition(SpecDefinition {
            name: "kernel_infer_const_sound".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (n : Name) (us : ListType Level) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInputAdmissible st (KExpr.const n us) -> ",
                "KernelInferAccepts st (KExpr.const n us) T -> ",
                "has_type (KExpr.const n us) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (n : Name) (us : ListType Level) (T : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelInputAdmissible st (KExpr.const n us)) ",
                    "(hinfer : KernelInferAccepts st (KExpr.const n us) T) => ",
                    "kernel_infer_inversion st (KExpr.const n us) T hinfer henv hctx hadm"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Forward simulation for kernel inference on constant expressions in the current const+delta fragment. DERIVED from the faithful KernelInferAccepts inductive via kernel_infer_inversion: the const constructor carries exactly this guarded implication, and the derivation applies it to this lemma's own guard premises — preserving the old axiom's guarded strength verbatim. Part of #2895, #461, Step 3.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelInferAccepts".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
                "has_type".to_string(),
            ])),
            // Residual closure through the master inversion: the 10 infer-band
            // skolems + KernelCheckAccepts (debt golden tracks this).
            axiom_deps: HashSet::new(),
        })?;

        // kernel_infer_sort_result: formerly a HelperAxiom, now DERIVED from the
        // faithful KernelInferAccepts inductive — the sort constructor's single
        // field IS this (unguarded, exactly as the old axiom) exact-result
        // equation, recovered by the master inversion.
        self.add_definition(SpecDefinition {
            name: "kernel_infer_sort_result".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (l : Level) (T : KExpr), ",
                "KernelInferAccepts st (KExpr.sort l) T -> ",
                "Eq KExpr (KExpr.sort (Level.succ l)) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    // The inversion yields the Type-valued KExprEqT universe
                    // adapter (the InferInversionAt payload family must live
                    // uniformly in Type); KExprEqT.rec + Eq.refl converts it
                    // back to the byte-identical Prop equation the old axiom
                    // concluded.
                    "fun (st : KernelState) (l : Level) (T : KExpr) ",
                    "(hinfer : KernelInferAccepts st (KExpr.sort l) T) => ",
                    "KExprEqT.rec (KExpr.sort (Level.succ l)) ",
                    "(fun (y : KExpr) (_h : KExprEqT (KExpr.sort (Level.succ l)) y) => ",
                    "Eq KExpr (KExpr.sort (Level.succ l)) y) ",
                    "(Eq.refl KExpr (KExpr.sort (Level.succ l))) ",
                    "T ",
                    "(kernel_infer_inversion st (KExpr.sort l) T hinfer)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Exact result of kernel's sort case: infer_type on Sort(l) returns ",
                "Sort(l+1). Directly verifiable from clean-kernel/src/tc/infer.rs ",
                "sort arm: ExprKind::Sort(l) => Sort(succ(l)). DERIVED from the ",
                "faithful KernelInferAccepts inductive via kernel_infer_inversion ",
                "(the sort constructor carries exactly this equation, unguarded as ",
                "the old axiom was; the KExprEqT universe adapter is converted back ",
                "to the Prop equation by KExprEqT.rec + Eq.refl). Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferAccepts".to_string(),
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
                "KExprEqT.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            // Residual closure through the master inversion: the 10 infer-band
            // skolems + KernelCheckAccepts (debt golden tracks this).
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_infer_sort_sound".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (l : Level) (T : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelInferAccepts st (KExpr.sort l) T -> ",
                "has_type (KExpr.sort l) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (l : Level) (T : KExpr) ",
                    "(_henv : KernelStateEnvValid st) ",
                    "(_hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hinfer : KernelInferAccepts st (KExpr.sort l) T) => ",
                    "Eq.substType KExpr (fun (X : KExpr) => Typing (KExpr.sort l) X) ",
                    "(KExpr.sort (Level.succ l)) T ",
                    "(kernel_infer_sort_result st l T hinfer) ",
                    "(Typing.sort l)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Forward simulation for the sort case: kernel inference on Sort(l) ",
                "yields has_type (Sort l) T. Constructive proof: the exact-result ",
                "axiom gives T = Sort(l+1), then Typing.sort l provides the typing ",
                "derivation, transported along the equality. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_infer_sort_result".to_string(),
                "Typing.sort".to_string(),
                "Eq.substType".to_string(),
            ])),
            // kernel_infer_sort_result is no longer an axiom leaf (derived via
            // kernel_infer_inversion); expand through to the master inversion's
            // residual closure: the 10 infer-band skolems + KernelCheckAccepts.
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // InferSoundAt: named motive for KExpr.rec dispatch (#461)
        // =========================================================
        //
        // By packaging the per-expression soundness predicate as a named
        // semireducible definition KExpr -> Type, the KExpr.rec dispatch
        // avoids the inline motive lambda that caused the discriminant
        // mismatch (beta-reduction of `(fun x => ...) (KExpr.sort l)`
        // in IH types). With InferSoundAt as a named constant, the
        // recursor sees `InferSoundAt f` rather than an unreduced
        // motive application, sidestepping the Discriminant(6) vs (3) issue.

        self.add_definition_reducible(SpecDefinition {
            name: "InferSoundAt".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (x : KExpr) => ",
                    "forall (st : KernelState) (T : KExpr), ",
                    "KernelStateEnvValid st -> ",
                    "KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st x -> ",
                    "KernelInferAccepts st x T -> ",
                    "has_type x T"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible motive alias for the KExpr.rec dispatch in ",
                "kernel_infer_returns_well_typed. Packages the per-expression ",
                "soundness predicate as a single-argument function KExpr -> Type, ",
                "avoiding inline motive beta-reduction in the recursor. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelInferAccepts".to_string(),
                "has_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Lam and pi per-case sound theorems are now in the binder module:
        // implementation_soundness_infer_refinement_binder.rs (#2869)
        //
        // kernel_infer_returns_well_typed dispatcher is now in:
        // implementation_soundness_infer_refinement_dispatch.rs

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_refinement_tests.rs"]
mod implementation_soundness_infer_refinement_tests;

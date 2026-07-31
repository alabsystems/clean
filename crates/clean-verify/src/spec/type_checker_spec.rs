// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! High-level formal specification for the public type-checker API.
//!
//! This module packages the existing implementation-soundness theorems into a
//! single `TypeCheckerSpec` surface for issue #462. The intent is to expose the
//! public algorithmic contracts of `TypeChecker::{check_type, infer_type,
//! is_def_eq}` without re-encoding the lower-level decomposition already proved
//! in `core_spec`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

pub use super::type_checker_spec_algorithm::{
    check_defeq_spec, check_type_spec, CompletenessWitness, DefeqAlgorithm, TypeCheckStep,
};

fn deps<const N: usize>(names: [&str; N]) -> HashSet<String> {
    names.into_iter().map(str::to_string).collect()
}

fn infer_axiom_deps() -> HashSet<String> {
    // The six per-case infer axioms (and the opaque KernelInferAccepts token)
    // are no longer axiom leaves — KernelInferAccepts is a faithful inductive
    // (Step 3) and all six per-case lemmas are derived from it via
    // kernel_infer_inversion. The check band (KernelCheckAccepts /
    // kernel_check_decomposition / kernel_check_types_admissible) is likewise
    // no longer a set of axiom leaves — KernelCheckAccepts is a faithful
    // inductive (Step 4) and both check axioms are derived via
    // KernelCheckAccepts.rec. Since the KernelInferResult un-Skolemization the
    // last infer-band skolem is GONE too: the inferred subtypes Rf/Ra are bound
    // existentially inside AppInferDecomp / the app constructor, and the shared
    // inferred type R inside KernelCheckAccepts.mk / CheckDecomp. The only
    // residual named leaf is the DerivedPending infer dispatcher
    // kernel_infer_returns_well_typed.
    deps(["kernel_infer_returns_well_typed"])
}

fn check_axiom_deps() -> HashSet<String> {
    // Since Step 4 the check band expands through the faithful
    // KernelCheckAccepts inductive to the same skolem-witness closure as the
    // infer side (the mk constructor's fields carry an infer acceptance at
    // KernelInferResult st e and a defeq acceptance on the inferred/expected
    // pair).
    infer_axiom_deps()
}

/// Formal surface of the public type-checker API.
#[derive(Debug, Clone)]
pub struct TypeCheckerSpec {
    definitions: Vec<SpecDefinition>,
}

impl TypeCheckerSpec {
    /// Build the high-level type-checker specification items.
    #[must_use]
    pub fn new() -> Self {
        Self {
            definitions: vec![
                SpecDefinition {
                    name: "tc_check_type_rule".to_string(),
                    type_src: concat!(
                        "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                        "KernelStateMatchesSpec st -> ",
                        "KernelInputAdmissible st e -> ",
                        "KernelCheckAccepts st e T -> ",
                        "has_type e T"
                    )
                    .to_string(),
                    value_src: Some(
                        concat!(
                            "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                            "(hmatch : KernelStateMatchesSpec st) ",
                            "(hadm : KernelInputAdmissible st e) ",
                            "(hcheck : KernelCheckAccepts st e T) => ",
                            "KernelCheckSound_summary st e T hmatch hadm hcheck"
                        )
                        .to_string(),
                    ),
                    is_axiom: false,
                    description: "Formal `check_type` rule: in a valid kernel state, successful algorithmic checking of `e` against `T` witnesses the specification typing judgment `has_type e T` in the corresponding context. Part of #462.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    // PROOF STATUS: DerivedProved — pure wrapper that delegates
                    // to `KernelCheckSound_summary` (DerivedLemma) with no new
                    // axioms. Library proof term registered in
                    // `proofs/library_type_checker_spec.rs`. axiom_deps equal
                    // the static `check_axiom_deps()` closure. Part of #462
                    // Packet C.
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps([
                        "KernelCheckSound_summary",
                        "KernelStateMatchesSpec",
                        "KernelInputAdmissible",
                        "KernelCheckAccepts",
                        "has_type",
                    ])),
                    axiom_deps: check_axiom_deps(),
                },
                SpecDefinition {
                    name: "tc_infer_type_rule".to_string(),
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
                            "(hmatch : KernelStateMatchesSpec st) ",
                            "(hadm : KernelInputAdmissible st e) ",
                            "(hinfer : KernelInferAccepts st e T) => ",
                            "KernelInferSound_summary st e T hmatch hadm hinfer"
                        )
                        .to_string(),
                    ),
                    is_axiom: false,
                    description: "Formal `infer_type` rule: in a valid kernel state, every algorithmic inference result is a specification typing derivation for the input expression. Part of #462.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    // PROOF STATUS: DerivedProved — pure wrapper that delegates
                    // to `KernelInferSound_summary` (DerivedLemma) with no new
                    // axioms. Library proof term registered in
                    // `proofs/library_type_checker_spec.rs`. axiom_deps equal
                    // the static `infer_axiom_deps()` closure. Part of #462
                    // Packet C.
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps([
                        "KernelInferSound_summary",
                        "KernelStateMatchesSpec",
                        "KernelInputAdmissible",
                        "KernelInferAccepts",
                        "has_type",
                    ])),
                    axiom_deps: infer_axiom_deps(),
                },
                SpecDefinition {
                    name: "tc_is_def_eq_rule".to_string(),
                    type_src: concat!(
                        "forall (st : KernelState) (e1 : KExpr) (e2 : KExpr), ",
                        "KernelStateMatchesSpec st -> ",
                        "KernelBinaryInputAdmissible st e1 e2 -> ",
                        "KernelDefEqAccepts st e1 e2 -> ",
                        "is_def_eq e1 e2"
                    )
                    .to_string(),
                    value_src: Some(
                        concat!(
                            "fun (st : KernelState) (e1 : KExpr) (e2 : KExpr) ",
                            "(hmatch : KernelStateMatchesSpec st) ",
                            "(hadm : KernelBinaryInputAdmissible st e1 e2) ",
                            "(hdefeq : KernelDefEqAccepts st e1 e2) => ",
                            "KernelDefEqSound_summary st e1 e2 hmatch hadm hdefeq"
                        )
                        .to_string(),
                    ),
                    is_axiom: false,
                    description: "Formal `is_def_eq` rule: in a valid kernel state, successful algorithmic definitional equality checking reflects the specification judgment `is_def_eq`. Part of #462.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    // PROOF STATUS: DerivedProved — pure wrapper that delegates
                    // to `KernelDefEqSound_summary` (DerivedLemma) with no new
                    // axioms. Library proof term registered in
                    // `proofs/library_type_checker_spec.rs`. axiom_deps are the
                    // minimal DefEq leaf closure (the two normalization skolem
                    // witnesses; kernel_defeq_decomposition is now derived via
                    // KernelDefEqAccepts.rec). Part of #462 Packet C.
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps([
                        "KernelDefEqSound_summary",
                        "KernelStateMatchesSpec",
                        "KernelBinaryInputAdmissible",
                        "KernelDefEqAccepts",
                        "is_def_eq",
                    ])),
                    axiom_deps: deps([
                    ]),
                },
                SpecDefinition {
                    name: "tc_infer_soundness".to_string(),
                    // Census-11 drain (Stage 2B-iii): the type now CARRIES the four
                    // env-closedness interfaces i3 : RecEnvClosed / i4 : RecEnvLiftClosed
                    // (red_rec the_red_env) and i5 : DefEnvClosed / i6 : DefEnvLiftClosed
                    // (red_def the_red_env) as SCHEMATIC TYPE hypotheses — a genuine
                    // (strengthened-premise, so soundness-safe) statement change, matching
                    // the schematic-discipline of join_compose / kernel_whnf_preserves_typing.
                    // They are NOT discharged over the_red_env's placeholder value
                    // (Guard-3 masquerade avoidance) — they are carried, never consumed.
                    type_src: concat!(
                        "forall (i3 : RecEnvClosed (red_rec the_red_env)) ",
                        "(i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                        "(i5 : DefEnvClosed (red_def the_red_env)) ",
                        "(i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                        "(st : KernelState) (e : KExpr) (T : KExpr), ",
                        "KernelStateMatchesSpec st -> ",
                        "KernelInputAdmissible st e -> ",
                        "KernelInferAccepts st e T -> ",
                        "KernelCheckAccepts st e T"
                    )
                    .to_string(),
                    value_src: Some(
                        concat!(
                            "fun (i3 : RecEnvClosed (red_rec the_red_env)) ",
                            "(i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
                            "(i5 : DefEnvClosed (red_def the_red_env)) ",
                            "(i6 : DefEnvLiftClosed (red_def the_red_env)) ",
                            "(st : KernelState) (e : KExpr) (T : KExpr) ",
                            "(hmatch : KernelStateMatchesSpec st) ",
                            "(hadm : KernelInputAdmissible st e) ",
                            "(hinfer : KernelInferAccepts st e T) => ",
                            // KernelCheckAccepts.mk with R := T: infer half = the
                            // hypothesis hinfer; defeq half = KernelDefEqAccepts.mk st T T
                            // whose guard yields a reflexive DefEqJoinable; admissibility
                            // guard = infer_result_self_admissible (inferred type of a
                            // closed input is itself closed).
                            "KernelCheckAccepts.mk st e T T ",
                            "(ProdType.mk (KernelInferAccepts st e T) (KernelDefEqAccepts st T T) ",
                            "hinfer ",
                            "(KernelDefEqAccepts.mk st T T ",
                            "(fun (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) ",
                            "(hbadm : KernelBinaryInputAdmissible st T T) => ",
                            "DefEqJoinable.mk T T T T (DefEq.refl T) (DefEq.refl T) (DefEq.refl T)))) ",
                            "(fun (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) ",
                            "(hadm2 : KernelInputAdmissible st e) => ",
                            "infer_result_self_admissible i3 i4 i5 i6 st e T henv hctx hinfer hadm2)"
                        )
                        .to_string(),
                    ),
                    is_axiom: false,
                    description: "Algorithmic soundness/introduction rule for the public API: when `infer_type` returns `T`, `check_type` also accepts `e` against that same inferred result. Census-11 drain (Stage 2B-iii): DRAINED from a HelperAxiom to a DerivedProved theorem (FlagAxiom 1->0, census 12->11 — the 3-axiom finish line). Value = KernelCheckAccepts.mk with R:=T: the infer half is the hypothesis `hinfer`, the defeq half is `KernelDefEqAccepts.mk st T T` (its guard yields the reflexive `DefEqJoinable.mk` via `DefEq.refl T`), and the admissibility guard is `infer_result_self_admissible` (the inferred type of a closed input is itself closed, by depth-0 `infer_preserves_closed`). The type CARRIES the four env-closedness interfaces i3/i4 (red_rec the_red_env) and i5/i6 (red_def the_red_env) as schematic TYPE hypotheses (the schematic-discipline drain, matching join_compose / kernel_whnf_preserves_typing) — a strengthened premise, so no soundness conclusion is weakened; the interfaces are carried, never discharged over the_red_env's placeholder value. Part of #462.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps([
                        "KernelCheckAccepts.mk",
                        "ProdType.mk",
                        "KernelDefEqAccepts.mk",
                        "DefEqJoinable.mk",
                        "DefEq.refl",
                        "infer_result_self_admissible",
                        "KernelStateMatchesSpec",
                        "KernelInputAdmissible",
                        "KernelInferAccepts",
                        "KernelCheckAccepts",
                        "RecEnvClosed",
                        "RecEnvLiftClosed",
                        "DefEnvClosed",
                        "DefEnvLiftClosed",
                        "red_rec",
                        "red_def",
                        "the_red_env",
                    ])),
                    axiom_deps: deps([]),
                },
                SpecDefinition {
                    name: "tc_check_completeness".to_string(),
                    type_src: concat!(
                        "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                        "KernelStateMatchesSpec st -> ",
                        "KernelInputAdmissible st e -> ",
                        "KernelCheckAccepts st e T -> ",
                        "CheckDecomp st e T"
                    )
                    .to_string(),
                    value_src: Some(
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
                        )
                        .to_string(),
                    ),
                    is_axiom: false,
                    description: "Completeness of `check_type` relative to the algorithm: if checking accepts `e` against `T`, then inference returns some result R (bound existentially in the CheckDecomp witness — the un-Skolemization retiring KernelInferResult st e) and the checker establishes definitional equality between R and `T`. This is intentionally phrased modulo definitional equality, which matches the implementation. Proved by eliminating KernelCheckAccepts.rec directly and repackaging the (R, ProdType-pair) into CheckDecomp.mk. Part of #462.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    // PROOF STATUS: DerivedProved — eliminates KernelCheckAccepts.rec
                    // directly (binding the inferred type R existentially) and
                    // repackages into the CheckDecomp witness, with no new axioms.
                    // Library proof term registered in
                    // `proofs/library_type_checker_spec.rs`. Skolem-free after the
                    // KernelInferResult un-Skolemization. Part of #462 Packet C.
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps([
                        "KernelCheckAccepts",
                        "KernelCheckAccepts.rec",
                        "CheckDecomp",
                        "CheckDecomp.mk",
                        "KernelInferAccepts",
                        "KernelDefEqAccepts",
                        "KernelStateMatchesSpec",
                        "KernelInputAdmissible",
                    ])),
                    axiom_deps: deps([]),
                },
                SpecDefinition {
                    name: "tc_def_eq_transitivity".to_string(),
                    type_src: "forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), is_def_eq e1 e2 -> is_def_eq e2 e3 -> is_def_eq e1 e3".to_string(),
                    value_src: Some(
                        "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) (h12 : is_def_eq e1 e2) (h23 : is_def_eq e2 e3) => def_eq_trans e1 e2 e3 h12 h23".to_string(),
                    ),
                    is_axiom: false,
                    description: "Transitivity of formal definitional equality. This is the metatheoretic transitivity property used by the algorithmic `is_def_eq` checker. Part of #462.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    // PROOF STATUS: DerivedProved — wraps `def_eq_trans`, which
                    // is itself DerivedProved with empty axiom_deps (alias for
                    // DefEq.trans). The proof term `fun ... => def_eq_trans e1
                    // e2 e3 h12 h23` kernel-type-checks through `add_decl`
                    // (`prepare_definition_decl` elaborates both type_src and
                    // value_src and infers inferred-type def-eq to type_src),
                    // and `ProofLibrary::audit_dependencies` classifies it as
                    // DerivedProved because the only referenced constant
                    // (`def_eq_trans`) is DerivedProved. #462 Packet A.
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps(["def_eq_trans", "is_def_eq"])),
                    axiom_deps: HashSet::new(),
                },
                SpecDefinition {
                    name: "tc_subject_reduction".to_string(),
                    type_src: "forall (hf : RedEnvFaithful the_red_env) (e : KExpr) (T : KExpr) (e' : KExpr), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> has_type e T -> whnf_to e e' -> has_type e' T".to_string(),
                    value_src: Some(
                        "fun (hf : RedEnvFaithful the_red_env) (e : KExpr) (T : KExpr) (e' : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (ht : has_type e T) (hred : whnf_to e e') => whnf_to_preserves_typing hf e e' T wd wr hred ht".to_string(),
                    ),
                    is_axiom: false,
                    description: "Subject reduction over the checker's DIRECTED reduction relation: if `e` has type `T` and `e` whnf-reduces to `e'`, then `e'` still has type `T`. Restated forward over whnf_to (the genuine, kernel-faithful subject reduction); the former symmetric is_def_eq form is unsound under untyped beta. church_rosser_whnf retirement track.".to_string(),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedPending,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(deps([
                        "whnf_to_preserves_typing",
                        "has_type",
                        "whnf_to",
                    ])),
                    axiom_deps: HashSet::new(),
                },
            ],
        }
    }

    /// Borrow the specification definitions in registration order.
    #[must_use]
    pub fn definitions(&self) -> &[SpecDefinition] {
        &self.definitions
    }

    fn register(&self, spec: &mut Specification) -> Result<(), SpecError> {
        for def in &self.definitions {
            spec.add_definition(def.clone())?;
        }
        Ok(())
    }
}

impl Default for TypeCheckerSpec {
    fn default() -> Self {
        Self::new()
    }
}

impl Specification {
    pub(super) fn add_type_checker_spec(&mut self) -> Result<(), SpecError> {
        TypeCheckerSpec::new().register(self)
    }
}

#[cfg(test)]
#[path = "type_checker_spec_tests.rs"]
mod type_checker_spec_tests;

#[cfg(test)]
#[path = "type_checker_spec_algorithm_tests.rs"]
mod type_checker_spec_algorithm_tests;

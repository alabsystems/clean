// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The actual assembled model theorem at one universe-dependent signature.
//! This establishes applicability of the model bridge, not Rust execution or
//! a valid admitted production environment.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn constant_theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    pub(super) fn add_impl_constant_soundness_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_constant_inference_correctness()?;
        let tenv = "schematic_tenv_witness_impl";
        let tenvk = "schematic_tenv_witness_kernel";
        let ci = "schematic_tenv_witness_ci";
        let us = "(@ListType.cons Level u (@ListType.nil Level))";
        let subject = format!("(ImplExpr.const Name.anonymous {us})");
        let derivation = format!(
            "(@ImplInfer.const {tenv} (@ListType.nil Name) Nat.zero LCtx.nil \
             Name.anonymous {us} {ci} \
             (@Eq.refl (OptionType ImplConstInfo) (@OptionType.some ImplConstInfo {ci})) \
             (@Eq.refl Nat (Nat.succ Nat.zero)) levels \
             (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.false))"
        );
        self.add_definition(SpecDefinition {
            name: "impl_infer_sound_polymorphic_constant".to_string(),
            type_src: format!(
                "forall (u : Level), @Eq Bool (impl_levels_ok (@ListType.nil Name) {us}) Bool.true -> \
                 TypingCtxConv {tenvk} (@ListType.nil KExpr) (KExpr.const Name.anonymous {us}) (KExpr.sort u)"
            ),
            value_src: Some(format!(
                "fun (u : Level) (levels : @Eq Bool (impl_levels_ok (@ListType.nil Name) {us}) Bool.true) => \
                 impl_infer_sound {tenv} {tenvk} (@ListType.nil Name) \
                 schematic_tenv_polymorphic_witness Nat.zero LCtx.nil {subject} \
                 (ImplExpr.sort u) Nat.zero {derivation} ImplUnit.mk \
                 (@ListType.nil Nat) (@ListType.nil KExpr) ctx_rep_nil_witness"
            )),
            is_axiom: false,
            description: "Apply the actual assembled impl_infer_sound theorem to one stored polymorphic signature at every model-valid closed level. Model lookup, exact arity, mode flags, schematic representation, inference guard, and empty context representation are constructed explicitly. The result type depends on u; no fixed-type premise remains. This is not source refinement or declaration admission.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;
        for (suffix, level) in [("zero", "Level.zero"), ("one", "(Level.succ Level.zero)")] {
            self.add_definition(SpecDefinition {
                name: format!("impl_infer_sound_constant_{suffix}"),
                type_src: format!(
                    "TypingCtxConv {tenvk} (@ListType.nil KExpr) \
                     (KExpr.const Name.anonymous (@ListType.cons Level {level} (@ListType.nil Level))) \
                     (KExpr.sort {level})"
                ),
                value_src: Some(format!(
                    "impl_infer_sound_polymorphic_constant {level} (@Eq.refl Bool Bool.true)"
                )),
                is_axiom: false,
                description: "The same schematic environment and assembled inference theorem produce this universe-specific type, with the level-validity premise also discharged.".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// Invert the actual inference relation, rather than only testing the
    /// standalone lookup function. No declarative-conversion claim is made.
    fn add_constant_inference_correctness(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive ConstantInferReturn (tenv : KDeclEnv) (n : Name)
(us : ListType Level) (T : KExpr) : Type
| intro : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr T) -> ConstantInferReturn tenv n us T",
            "Type-valued wrapper for the exact guarded constant lookup equation. Nonconstant inference subjects make no claim.",
        )?;
        self.add_recursive_def(
            r"def constant_infer_result (tenv : KDeclEnv) (e : KExpr) (T : KExpr) : Type := match e with
| KExpr.sort u => Nat
| KExpr.bvar i => Nat
| KExpr.app f a => Nat
| KExpr.lam A b => Nat
| KExpr.pi A B => Nat
| KExpr.const n us => ConstantInferReturn tenv n us T
| KExpr.let_ A v b => Nat
| KExpr.proj sn i sub => Nat
| KExpr.lit n => Nat",
            "The exact constant-return assertion for a constant subject; deliberately trivial for every other expression constructor.",
        )?;
        constant_theorem(
            self,
            "kernelinfers_constant_result",
            r"forall (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr),
KernelInfers tenv G e T -> constant_infer_result tenv e T",
            r"fun (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : KernelInfers tenv G e T) =>
@KernelInfers.rec tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
    (_h : KernelInfers tenv G0 e0 T0) => constant_infer_result tenv e0 T0)
  (fun (_G0 : ListType KExpr) (_u : Level) => Nat.zero)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
    (_hl : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr)
    (u : Level) (SB : KExpr) (v : Level)
    (_ha : KernelInfers tenv G0 A SA) (_hwa : whnf_to SA (KExpr.sort u))
    (_hb : KernelInfers tenv (@ListType.cons KExpr A G0) B SB)
    (_hwb : whnf_to SB (KExpr.sort v))
    (_iha : constant_infer_result tenv A SA) (_ihb : constant_infer_result tenv B SB) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr)
    (SA : KExpr) (u : Level) (_ha : KernelInfers tenv G0 A SA)
    (_hw : whnf_to SA (KExpr.sort u))
    (_hb : KernelInfers tenv (@ListType.cons KExpr A G0) b B)
    (_iha : constant_infer_result tenv A SA) (_ihb : constant_infer_result tenv b B) => Nat.zero)
  (fun (_G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
    (hl : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) =>
      @ConstantInferReturn.intro tenv n us A hl)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr)
    (A : KExpr) (B : KExpr) (A2 : KExpr) (_hf : KernelInfers tenv G0 f F)
    (_hw : whnf_to F (KExpr.pi A B)) (_ha : KernelInfers tenv G0 a A2)
    (_heq : DefEq A2 A) (_ihf : constant_infer_result tenv f F)
    (_iha : constant_infer_result tenv a A2) => Nat.zero)
  (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr)
    (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelInfers tenv G0 ty Ty) (_hw : whnf_to Ty (KExpr.sort u))
    (_hv : KernelInfers tenv G0 v Tv) (_heq : DefEq Tv ty)
    (_hb : KernelInfers tenv (@ListType.cons KExpr ty G0) b B)
    (_iht : constant_infer_result tenv ty Ty) (_ihv : constant_infer_result tenv v Tv)
    (_ihb : constant_infer_result tenv b B) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero) G e T h",
            "Inversion over every actual KernelInfers constructor retains the guarded lookup equation at a constant subject. No alternate algorithmic rule can bypass missing-name or arity failure.",
        )?;
        constant_theorem(
            self,
            "kernelinfers_constant_lookup",
            r"forall (tenv : KDeclEnv) (G : ListType KExpr) (n : Name)
(us : ListType Level) (T : KExpr), KernelInfers tenv G (KExpr.const n us) T ->
@Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr T)",
            r"fun (tenv : KDeclEnv) (G : ListType KExpr) (n : Name)
(us : ListType Level) (T : KExpr) (h : KernelInfers tenv G (KExpr.const n us) T) =>
@ConstantInferReturn.rec tenv n us T
  (fun (_h : ConstantInferReturn tenv n us T) =>
    @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr T))
  (fun (eq : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr T)) => eq)
  (kernelinfers_constant_result tenv G (KExpr.const n us) T h)",
            "A successful constant inference must have the exact computed instantiated type returned by guarded lookup, for arbitrary environments and contexts.",
        )?;
        constant_theorem(
            self,
            "kernelinfers_constant_lookup_failure",
            r"forall (tenv : KDeclEnv) (G : ListType KExpr) (n : Name)
(us : ListType Level) (T : KExpr),
@Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.none KExpr) ->
KernelInfers tenv G (KExpr.const n us) T -> Empty",
            r"fun (tenv : KDeclEnv) (G : ListType KExpr) (n : Name)
(us : ListType Level) (T : KExpr)
(missing : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.none KExpr))
(h : KernelInfers tenv G (KExpr.const n us) T) =>
option_none_ne_some_type KExpr T Empty
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (kdecl_type_at tenv n us)
    (@OptionType.some KExpr T)
    (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.none KExpr) missing)
    (kernelinfers_constant_lookup tenv G n us T h))",
            "Failed guarded lookup excludes an inference derivation with every claimed result type. This is a theorem about the algorithmic model, not a finite lookup test.",
        )?;
        constant_theorem(
            self,
            "kernelinfers_constant_wrong_arity",
            r"forall (tenv : KDeclEnv) (G : ListType KExpr) (n : Name)
(us : ListType Level) (sig : KConstSig) (T : KExpr),
@Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
(kconst_arity sig us -> Empty) -> KernelInfers tenv G (KExpr.const n us) T -> Empty",
            r"fun (tenv : KDeclEnv) (G : ListType KExpr) (n : Name)
(us : ListType Level) (sig : KConstSig) (T : KExpr)
(get : @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig))
(bad : kconst_arity sig us -> Empty) =>
kernelinfers_constant_lookup_failure tenv G n us T (kdecl_type_at_wrong_arity tenv n us sig get bad)",
            "An existing declaration with wrong universe arity cannot infer any type; derived through actual lookup failure and inversion of KernelInfers.",
        )?;
        constant_theorem(
            self,
            "kernelinfers_polymorphic_missing_argument",
            r"forall (G : ListType KExpr) (T : KExpr),
KernelInfers schematic_tenv_witness_kernel G (KExpr.const Name.anonymous (@ListType.nil Level)) T -> Empty",
            r"fun (G : ListType KExpr) (T : KExpr) =>
kernelinfers_constant_lookup_failure schematic_tenv_witness_kernel G Name.anonymous
  (@ListType.nil Level) T schematic_tenv_missing_arity_witness",
            "The same inhabited polymorphic signature used by the assembled positive witnesses cannot infer any type with its universe argument missing. No extra invariant premise excludes this case.",
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::build_spec_with_stack;

    #[test]
    fn assembled_soundness_applies_to_one_polymorphic_signature_at_distinct_levels() {
        let spec = build_spec_with_stack();
        for name in [
            "impl_infer_sound_polymorphic_constant",
            "impl_infer_sound_constant_zero",
            "impl_infer_sound_constant_one",
        ] {
            let def = spec.definitions().get(name).expect("registered witness");
            assert!(!def.is_axiom);
            assert_eq!(def.proof_status, ProofStatus::DerivedProved);
            assert!(def.elaborated_value.is_some());
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
            assert!(def
                .value_src
                .as_deref()
                .is_some_and(|value| value.contains("impl_infer_sound")));
        }
    }

    #[test]
    fn constant_inference_cannot_bypass_guarded_lookup() {
        let spec = build_spec_with_stack();
        for name in [
            "kernelinfers_constant_result",
            "kernelinfers_constant_lookup",
            "kernelinfers_constant_lookup_failure",
            "kernelinfers_constant_wrong_arity",
            "kernelinfers_polymorphic_missing_argument",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .expect("registered constant inversion");
            assert!(!def.is_axiom);
            assert_eq!(def.proof_status, ProofStatus::DerivedProved);
            assert!(def.elaborated_value.is_some());
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
        }
    }
}

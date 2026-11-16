// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Schematic environment correspondence, with instantiated lookup derived.
//!
//! A successful implementation-model lookup identifies one stored signature.
//! No per-universe output equation is assumed: the computed lookup theorem
//! follows from arity, the raw instantiation bridge, and No-FVar translation.
//! This does not assert Rust extraction, de Bruijn closure, universe support,
//! admissibility, or validity of the signature's type.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn schematic_env_theorem(
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
    /// Runs after lookup, raw instantiation, and No-FVar proofs, before M4.
    pub(super) fn add_schematic_tenv_rep(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def impl_schematic_signature (ci : ImplConstInfo) : KConstSig := KConstSig.mk (impl_const_lps ci) (to_kexpr (impl_const_type ci) (@ListType.nil Nat))",
            "One schematic signature translated at the empty renaming, retaining the actual ordered universe-parameter list.",
        )?;
        self.add_inductive(
            r"inductive ImplConstEnvEntryRep (ci : ImplConstInfo) : OptionType KConstSig -> Type
| mk : ImplNoFVar (impl_const_type ci) -> ImplConstEnvEntryRep ci (@OptionType.some KConstSig (impl_schematic_signature ci))",
            "Successful lookup representation identifies exactly one stored schematic signature and structurally rules out FVars in its implementation-model type. It does not assume any instantiated result or lexical closedness.",
        )?;
        self.add_recursive_def(
            r"def SchematicTEnvRep (tenv : Name -> OptionType ImplConstInfo) (tenvK : KDeclEnv) : Type :=
forall (nm : Name) (ci : ImplConstInfo), @Eq (OptionType ImplConstInfo) (tenv nm) (@OptionType.some ImplConstInfo ci) -> ImplConstEnvEntryRep ci (tenvK nm)",
            "One-way representation of successful implementation-model declaration lookup. An entry ties the stored parameter list and schematic type together; acceptance invariants remain separate.",
        )?;
        schematic_env_theorem(
            self,
            "impl_const_entry_signature",
            r"forall (ci : ImplConstInfo) (entry : OptionType KConstSig),
ImplConstEnvEntryRep ci entry -> @Eq (OptionType KConstSig) entry (@OptionType.some KConstSig (impl_schematic_signature ci))",
            r"fun (ci : ImplConstInfo) (entry : OptionType KConstSig) (h : ImplConstEnvEntryRep ci entry) =>
@ImplConstEnvEntryRep.rec ci
  (fun (entry0 : OptionType KConstSig) (_h : ImplConstEnvEntryRep ci entry0) =>
    @Eq (OptionType KConstSig) entry0 (@OptionType.some KConstSig (impl_schematic_signature ci)))
  (fun (_nf : ImplNoFVar (impl_const_type ci)) =>
    @Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig (impl_schematic_signature ci))) entry h",
            "Indexed entry inversion recovers the exact stored schematic signature, not an assumed dynamic lookup result.",
        )?;
        schematic_env_theorem(
            self,
            "impl_const_entry_no_fvar",
            r"forall (ci : ImplConstInfo) (entry : OptionType KConstSig),
ImplConstEnvEntryRep ci entry -> ImplNoFVar (impl_const_type ci)",
            r"fun (ci : ImplConstInfo) (entry : OptionType KConstSig) (h : ImplConstEnvEntryRep ci entry) =>
@ImplConstEnvEntryRep.rec ci
  (fun (_entry : OptionType KConstSig) (_h : ImplConstEnvEntryRep ci _entry) => ImplNoFVar (impl_const_type ci))
  (fun (nf : ImplNoFVar (impl_const_type ci)) => nf) entry h",
            "Recover the structural No-FVar witness needed for changing the translation renaming.",
        )?;
        schematic_env_theorem(
            self,
            "impl_schematic_instantiated_type",
            r"forall (ci : ImplConstInfo), ImplNoFVar (impl_const_type ci) ->
forall (us : ListType Level), @Eq Nat (name_list_len (impl_const_lps ci)) (level_list_len us) ->
forall (rho : ListType Nat),
@Eq KExpr (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho)
  (kconst_inst_type (impl_schematic_signature ci) us)",
            r"fun (ci : ImplConstInfo) (nf : ImplNoFVar (impl_const_type ci))
(us : ListType Level) (arity : @Eq Nat (name_list_len (impl_const_lps ci)) (level_list_len us))
(rho : ListType Nat) =>
Eq.trans KExpr
  (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho)
  (instLevels (impl_const_lps ci) (to_kexpr (impl_const_type ci) rho) us)
  (kconst_inst_type (impl_schematic_signature ci) us)
  (to_kexpr_impl_inst_levels (impl_const_lps ci) us arity (impl_const_type ci) rho)
  (Eq.cong KExpr KExpr (fun (ty : KExpr) => instLevels (impl_const_lps ci) ty us)
    (to_kexpr (impl_const_type ci) rho) (to_kexpr (impl_const_type ci) (@ListType.nil Nat))
    (to_kexpr_rho_independent (impl_const_type ci) nf rho (@ListType.nil Nat)))",
            "Derive the translated instantiated type from one schematic signature for every exact-arity universe list and renaming. Raw model-to-model theorem; not Rust substitution refinement.",
        )?;
        schematic_env_theorem(
            self,
            "schematic_tenv_lookup",
            r"forall (tenv : Name -> OptionType ImplConstInfo) (tenvK : KDeclEnv),
SchematicTEnvRep tenv tenvK -> forall (nm : Name) (ci : ImplConstInfo) (us : ListType Level) (rho : ListType Nat),
@Eq (OptionType ImplConstInfo) (tenv nm) (@OptionType.some ImplConstInfo ci) ->
@Eq Nat (name_list_len (impl_const_lps ci)) (level_list_len us) ->
@Eq (OptionType KExpr) (kdecl_type_at tenvK nm us)
  (@OptionType.some KExpr (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho))",
            r"fun (tenv : Name -> OptionType ImplConstInfo) (tenvK : KDeclEnv)
(rep : SchematicTEnvRep tenv tenvK) (nm : Name) (ci : ImplConstInfo) (us : ListType Level) (rho : ListType Nat)
(get : @Eq (OptionType ImplConstInfo) (tenv nm) (@OptionType.some ImplConstInfo ci))
(arity : @Eq Nat (name_list_len (impl_const_lps ci)) (level_list_len us)) =>
Eq.trans (OptionType KExpr) (kdecl_type_at tenvK nm us)
  (@OptionType.some KExpr (kconst_inst_type (impl_schematic_signature ci) us))
  (@OptionType.some KExpr (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho))
  (kdecl_type_at_intro tenvK nm (impl_schematic_signature ci) us
    (impl_const_entry_signature ci (tenvK nm) (rep nm ci get)) arity)
  (Eq.cong KExpr (OptionType KExpr) (fun (ty : KExpr) => @OptionType.some KExpr ty)
    (kconst_inst_type (impl_schematic_signature ci) us)
    (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho)
    (Eq.symm KExpr
      (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho)
      (kconst_inst_type (impl_schematic_signature ci) us)
      (impl_schematic_instantiated_type ci (impl_const_entry_no_fvar ci (tenvK nm) (rep nm ci get)) us arity rho)))",
            "Actual computed declaration lookup follows from schematic representation and arity. This replaces the former all-universes desired-output hypothesis with a derived equation.",
        )?;
        schematic_env_theorem(
            self,
            "schematic_tenv_empty",
            "SchematicTEnvRep (fun (_nm : Name) => @OptionType.none ImplConstInfo) (fun (_nm : Name) => @OptionType.none KConstSig)",
            r"fun (nm : Name) (ci : ImplConstInfo)
(get : @Eq (OptionType ImplConstInfo) (@OptionType.none ImplConstInfo) (@OptionType.some ImplConstInfo ci)) =>
option_none_ne_some_type ImplConstInfo ci (ImplConstEnvEntryRep ci (@OptionType.none KConstSig)) get",
            "Empty-environment representation is vacuous; the nonempty polymorphic witness is required separately to show the intended new scope.",
        )?;
        self.add_schematic_tenv_witnesses()
    }

    fn add_schematic_tenv_witnesses(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (
                "def schematic_tenv_witness_ci : ImplConstInfo := ImplConstInfo.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (ImplExpr.sort (Level.param Name.anonymous)) Bool.false Bool.false",
                "Nonempty schematic signature whose translated type changes when its supplied universe changes; not an admitted declaration witness.",
            ),
            (
                "def schematic_tenv_witness_impl : Name -> OptionType ImplConstInfo := fun (_nm : Name) => @OptionType.some ImplConstInfo schematic_tenv_witness_ci",
                "Nonempty implementation-model environment for the signature-correspondence witness.",
            ),
            (
                "def schematic_tenv_witness_kernel : KDeclEnv := fun (_nm : Name) => @OptionType.some KConstSig (impl_schematic_signature schematic_tenv_witness_ci)",
                "Matching schematic-signature environment; no fixed instantiated type is stored.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        schematic_env_theorem(
            self,
            "schematic_tenv_polymorphic_witness",
            "SchematicTEnvRep schematic_tenv_witness_impl schematic_tenv_witness_kernel",
            r"fun (nm : Name) (ci : ImplConstInfo)
(get : @Eq (OptionType ImplConstInfo) (@OptionType.some ImplConstInfo schematic_tenv_witness_ci) (@OptionType.some ImplConstInfo ci)) =>
Eq.substType ImplConstInfo
  (fun (ci0 : ImplConstInfo) => ImplConstEnvEntryRep ci0 (schematic_tenv_witness_kernel nm))
  schematic_tenv_witness_ci ci (option_some_inj ImplConstInfo schematic_tenv_witness_ci ci get)
  (@ImplConstEnvEntryRep.mk schematic_tenv_witness_ci (ImplNoFVar.sort (Level.param Name.anonymous)))",
            "Constructible nonempty environment relation for a genuinely universe-dependent type. The lookup recovers the record; no dynamic-result hypothesis is supplied.",
        )?;
        for (suffix, level) in [("zero", "Level.zero"), ("one", "(Level.succ Level.zero)")] {
            schematic_env_theorem(
                self,
                &format!("schematic_tenv_lookup_{suffix}_witness"),
                &format!(
                    "@Eq (OptionType KExpr) (kdecl_type_at schematic_tenv_witness_kernel Name.anonymous (@ListType.cons Level {level} (@ListType.nil Level))) (@OptionType.some KExpr (KExpr.sort {level}))"
                ),
                &format!(
                    "schematic_tenv_lookup schematic_tenv_witness_impl schematic_tenv_witness_kernel schematic_tenv_polymorphic_witness Name.anonymous schematic_tenv_witness_ci (@ListType.cons Level {level} (@ListType.nil Level)) (@ListType.nil Nat) (@Eq.refl (OptionType ImplConstInfo) (@OptionType.some ImplConstInfo schematic_tenv_witness_ci)) (@Eq.refl Nat (Nat.succ Nat.zero))"
                ),
                "The generic schematic lookup theorem computes this supplied universe, with all of its premises discharged by the same stored signature.",
            )?;
        }
        schematic_env_theorem(
            self,
            "schematic_tenv_missing_arity_witness",
            "@Eq (OptionType KExpr) (kdecl_type_at schematic_tenv_witness_kernel Name.anonymous (@ListType.nil Level)) (@OptionType.none KExpr)",
            "@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "The same nonempty represented signature refuses a missing universe argument; its raw default does not become a successful lookup.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn schematic_lookup_is_derived_with_empty_actual_axiom_closure() {
        let spec = build_spec_with_stack();
        for name in [
            "impl_const_entry_signature",
            "impl_const_entry_no_fvar",
            "impl_schematic_instantiated_type",
            "schematic_tenv_lookup",
            "schematic_tenv_empty",
            "schematic_tenv_polymorphic_witness",
            "schematic_tenv_lookup_zero_witness",
            "schematic_tenv_lookup_one_witness",
            "schematic_tenv_missing_arity_witness",
        ] {
            let def = spec.definitions().get(name).expect("registered theorem");
            assert!(!def.is_axiom);
            assert_eq!(def.proof_status, ProofStatus::DerivedProved);
            assert!(def.elaborated_value.is_some());
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
        }
    }

    #[test]
    fn schematic_entry_rejects_forged_signature_and_fvar_witnesses() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for (name, source) in [
                (
                    "schematic_entry_wrong_signature",
                    "def schematic_entry_wrong_signature : ImplConstEnvEntryRep schematic_tenv_witness_ci (@OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.sort Level.zero))) := @ImplConstEnvEntryRep.mk schematic_tenv_witness_ci (ImplNoFVar.sort (Level.param Name.anonymous))",
                ),
                (
                    "schematic_entry_fvar_false_witness",
                    "def schematic_entry_fvar_false_witness : ImplConstEnvEntryRep (ImplConstInfo.mk (@ListType.nil Name) (ImplExpr.fvar Nat.zero) Bool.false Bool.false) (@OptionType.some KConstSig (impl_schematic_signature (ImplConstInfo.mk (@ListType.nil Name) (ImplExpr.fvar Nat.zero) Bool.false Bool.false))) := @ImplConstEnvEntryRep.mk (ImplConstInfo.mk (@ListType.nil Name) (ImplExpr.fvar Nat.zero) Bool.false Bool.false) (ImplNoFVar.bvar Nat.zero)",
                ),
                (
                    "schematic_lookup_missing_argument_success",
                    "def schematic_lookup_missing_argument_success : @Eq (OptionType KExpr) (kdecl_type_at schematic_tenv_witness_kernel Name.anonymous (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.sort Level.zero)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))",
                ),
            ] {
                assert!(spec.add_recursive_def(source, "Negative control; must be rejected.").is_err());
                assert!(!spec.definitions().contains_key(name));
            }
        });
    }
}

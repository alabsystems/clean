// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computed declaration lookup under raw universe substitution.
//!
//! From a successful lookup, recover the actual schematic signature and arity;
//! preserve that arity and use support-sensitive instantiation fusion to derive
//! the new successful lookup. No equality about every instantiated output is
//! assumed. The query-local theorem needs support only at the queried name;
//! its environment-wide corollary matches a schematic environment invariant.
//!
//! Exact-export prototype and provenance:
//! scratch/self-verification-declaration-instantiation-2026-09-08.lean.
//! This is the constant-lookup prerequisite, not full typing/conversion
//! preservation, production admission, smart-level semantics, or Rust refinement.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn instantiation_theorem(
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
    /// General proofs follow declaration_signature_lookup and the general
    /// universe_support_fusion method, so they can precede subject reduction.
    /// Controls register separately at the later support-control frontier.
    pub(super) fn add_declaration_lookup_instantiation(&mut self) -> Result<(), SpecError> {
        instantiation_theorem(
            self,
            "kdecl_type_at_instL_supported_at",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (A : KExpr),
 @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr A) ->
 (forall (sig : KConstSig), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (s : Name -> Level),
 @Eq (OptionType KExpr) (kdecl_type_at env n (mapLL (substL s) us))
   (@OptionType.some KExpr (instL s A))",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (A : KExpr)
 (accepted : @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr A))
 (supported : forall (sig : KConstSig),
   @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (s : Name -> Level) =>
 kdecl_type_at_some_inv_prop env n us A accepted
   (@Eq (OptionType KExpr) (kdecl_type_at env n (mapLL (substL s) us))
     (@OptionType.some KExpr (instL s A)))
   (fun (sig : KConstSig)
     (found : @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig))
     (arity : kconst_arity sig us)
     (result : @Eq KExpr A (kconst_inst_type sig us)) =>
     @Eq.trans (OptionType KExpr)
       (kdecl_type_at env n (mapLL (substL s) us))
       (@OptionType.some KExpr (kconst_inst_type sig (mapLL (substL s) us)))
       (@OptionType.some KExpr (instL s A))
       (kdecl_type_at_intro env n sig (mapLL (substL s) us) found
         (arity_mapLL (kconst_params sig) us arity (substL s)))
       (@Eq.cong KExpr (OptionType KExpr)
         (fun (T : KExpr) => @OptionType.some KExpr T)
         (kconst_inst_type sig (mapLL (substL s) us)) (instL s A)
         (@Eq.trans KExpr
           (kconst_inst_type sig (mapLL (substL s) us))
           (instL s (kconst_inst_type sig us)) (instL s A)
           (@Eq.symm KExpr (instL s (kconst_inst_type sig us))
             (kconst_inst_type sig (mapLL (substL s) us))
             (instL_instLevels_supported (kconst_params sig) (kconst_type sig) us
               (supported sig found) s))
           (@Eq.cong KExpr KExpr (fun (T : KExpr) => instL s T)
             (kconst_inst_type sig us) A
             (@Eq.symm KExpr A (kconst_inst_type sig us) result)))))",
            "Computed successful declaration lookup commutes with universe substitution from support of the actual signature at the queried name. Inversion supplies real lookup, exact arity and the original result equation; mapped arity and supported fusion derive the new result. No per-instantiated-output law is assumed.",
        )?;

        instantiation_theorem(
            self,
            "kdecl_type_at_instL_supported",
            r"forall (env : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (n : Name) (us : ListType Level) (A : KExpr),
 @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr A) ->
 forall (s : Name -> Level),
 @Eq (OptionType KExpr) (kdecl_type_at env n (mapLL (substL s) us))
   (@OptionType.some KExpr (instL s A))",
            r"fun (env : KDeclEnv)
 (supported : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (n : Name) (us : ListType Level) (A : KExpr)
 (accepted : @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr A))
 (s : Name -> Level) =>
 kdecl_type_at_instL_supported_at env n us A accepted (supported n) s",
            "Environment-wide corollary: support is required only of each stored schematic signature under its own declared parameters. This discharges the computed constant-lookup case, not the other typing/conversion cases or production admission.",
        )?;

        Ok(())
    }

    /// Late controls: the unsupported-signature exclusion consumes the late support-fusion counterexample.
    pub(super) fn add_declaration_lookup_instantiation_controls(
        &mut self,
    ) -> Result<(), SpecError> {
        instantiation_theorem(
            self,
            "kdecl_type_at_instL_nonzero_witness",
            r"@Eq (OptionType KExpr)
 (kdecl_type_at (fun (_ : Name) => @OptionType.some KConstSig (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous
   (mapLL (substL (fun (_ : Name) => Level.succ Level.zero)) (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level))))
 (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
            r"kdecl_type_at_instL_supported_at (fun (_ : Name) => @OptionType.some KConstSig (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level)) (KExpr.sort (Level.param Name.anonymous))
 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous))))
 (fun (sig : KConstSig)
   (found : @Eq (OptionType KConstSig) (@OptionType.some KConstSig (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous))))
     (@OptionType.some KConstSig sig)) =>
   @Eq.rec KConstSig (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous)))
     (fun (other : KConstSig) (_h : @Eq KConstSig (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous))) other) =>
       KExprParamSupport (kconst_params other) (kconst_type other))
     (@KExprParamSupport.sort (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (Level.param Name.anonymous)
       (@LevelParamSupport.param (@ListType.cons Name Name.anonymous (@ListType.nil Name)) Name.anonymous Nat.zero
         (@Eq.refl (OptionType Nat) (@OptionType.some Nat Nat.zero))))
     sig (option_some_inj KConstSig (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous))) sig found))
 (fun (_ : Name) => Level.succ Level.zero)",
            "Positive computed-lookup control: a one-parameter schematic sort is instantiated at a parameter argument and then a nonzero universe. Support is constructed from actual singleton membership and lookup injectivity.",
        )?;

        instantiation_theorem(
            self,
            "kdecl_type_at_instL_unsupported_fails",
            r"@Eq (OptionType KExpr)
 (kdecl_type_at (fun (_ : Name) => @OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous
   (mapLL (substL (fun (_ : Name) => Level.zero)) (@ListType.nil Level)))
 (@OptionType.some KExpr (instL (fun (_ : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous)))) -> Empty",
            r"fun (h : @Eq (OptionType KExpr)
 (kdecl_type_at (fun (_ : Name) => @OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.param Name.anonymous)))) Name.anonymous
   (mapLL (substL (fun (_ : Name) => Level.zero)) (@ListType.nil Level)))
 (@OptionType.some KExpr (instL (fun (_ : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous))))) =>
 unsupported_fusion_fails
   (Eq.symm Level (Level.param Name.anonymous) Level.zero
     (kexpr_sort_inj (Level.param Name.anonymous) Level.zero
       (option_some_inj KExpr (KExpr.sort (Level.param Name.anonymous)) (KExpr.sort Level.zero) h)))",
            "Constructive refusal control: a successful exact-arity lookup whose schematic sort contains an undeclared parameter does not commute with substitution. The false equation implies Empty; lookup success alone cannot replace schematic support.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::instantiation_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn declaration_lookup_instantiation_has_checked_values_and_no_axiom_residuals() {
        let spec = build_spec_with_stack();
        for name in [
            "kdecl_type_at_instL_supported_at",
            "kdecl_type_at_instL_supported",
            "kdecl_type_at_instL_nonzero_witness",
            "kdecl_type_at_instL_unsupported_fails",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered lookup instantiation term");
            assert!(!definition.is_axiom, "{name} must have a proof");
            assert_eq!(definition.proof_status, ProofStatus::DerivedProved);
            assert!(
                definition.elaborated_value.is_some(),
                "{name} must be elaborated"
            );
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name} must have empty actual transitive axiom closure"
            );
        }
    }

    #[test]
    fn declaration_lookup_success_does_not_establish_schematic_support() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            // This concrete signature has no declared parameters but its type
            // contains one. Exact arity and lookup succeed nonetheless: the
            // raw graph itself is deliberately not an admission checker.
            let env = "(fun (_ : Name) => @OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.param Name.anonymous))))";
            instantiation_theorem(
                &mut spec,
                "lookup_unsupported_signature_still_accepts_original",
                &format!("@Eq (OptionType KExpr) (kdecl_type_at {env} Name.anonymous (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))"),
                "@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))",
                "Negative-control setup: lookup plus exact arity does not establish that schematic parameters were declared.",
            ).expect("the original raw lookup really succeeds");
            assert!(crate::spec_axiom_closure::computed_axiom_closure(
                &spec,
                "lookup_unsupported_signature_still_accepts_original"
            )
            .is_empty());
            assert!(instantiation_theorem(
                &mut spec,
                "lookup_unsupported_instantiation_must_fail",
                &format!("@Eq (OptionType KExpr) (kdecl_type_at {env} Name.anonymous (mapLL (substL (fun (_ : Name) => Level.zero)) (@ListType.nil Level))) (@OptionType.some KExpr (KExpr.sort Level.zero))"),
                "@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))",
                "Negative control: successful original lookup cannot fabricate the unsupported mapped-universe result.",
            ).is_err());
        });
    }
}

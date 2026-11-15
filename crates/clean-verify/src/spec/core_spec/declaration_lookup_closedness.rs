// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derive lookup-result closure from the stored schematic declaration type.
//!
//! Only the queried name's stored types are required to be de Bruijn closed.
//! No per-instantiated-result invariant, typing, actual declaration admission,
//! free-variable representation, or production-source correspondence is assumed.
//! The explicit terms are checked in the exact-export pinned Lean guide
//! scratch/self-verification-declaration-closedness-2026-09-08.lean.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn lookup_closedness_theorem(
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
    /// Requires declaration_signature_lookup, universe_closedness,
    /// lift_closed_at_id and le_zero_n. No typing judgment is used.
    pub(super) fn add_declaration_lookup_closedness(&mut self) -> Result<(), SpecError> {
        lookup_closedness_theorem(
            self,
            "kdecl_type_at_closed",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) (hstored : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero) (hlookup : Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T)), is_closed_at T Nat.zero",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) (hstored : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero) (hlookup : Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T)) =>
  kdecl_type_at_some_inv env n us T hlookup (is_closed_at T Nat.zero)
    (fun (sig : KConstSig)
      (hsig : Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig))
      (_harity : kconst_arity sig us)
      (hresult : Eq KExpr T (kconst_inst_type sig us)) =>
      Eq.substType KExpr (fun (e : KExpr) => is_closed_at e Nat.zero)
        (kconst_inst_type sig us) T (Eq.symm KExpr T (kconst_inst_type sig us) hresult)
        (instL_preserves_top_level_closed (paramSubstN (kconst_params sig) us)
          (kconst_type sig) (hstored sig hsig)))",
            "Successful computed lookup returns a top-level closed expression when the schematic type stored at this queried name is closed. Genuine lookup inversion and raw universe-instantiation preservation discharge the result property; no per-instantiated-result closure premise.",
        )?;
        lookup_closedness_theorem(
            self,
            "kdecl_type_at_psubst_closed",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) (hstored : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero) (hlookup : Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T)) (s : Nat -> KExpr), Eq KExpr (psubst s T) T",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) (hstored : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero) (hlookup : Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T)) (s : Nat -> KExpr) =>
  psubst_closed_id s T (kdecl_type_at_closed env n us T hstored hlookup)",
            "Every parallel substitution fixes the successful lookup result, derived from the stored schematic type's closedness and the existing psubst_closed_id theorem.",
        )?;
        lookup_closedness_theorem(
            self,
            "kdecl_type_at_lift_closed",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) (hstored : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero) (hlookup : Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T)) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at T cutoff amount) T",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) (hstored : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero) (hlookup : Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T)) (cutoff : Nat) (amount : Nat) =>
  lift_closed_at_id T Nat.zero (kdecl_type_at_closed env n us T hstored hlookup)
    cutoff amount (le_zero_n cutoff)",
            "Lifting at every cutoff and amount fixes the successful lookup result, derived from schematic closedness and the existing lift_closed_at_id theorem.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::lookup_closedness_theorem;
    use crate::spec::types::ProofStatus;
    use crate::spec::Specification;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    fn assert_checked_without_axioms(spec: &Specification, name: &str) {
        let definition = spec.definitions().get(name).expect("registered proof");
        assert!(!definition.is_axiom, "{name} must not be an axiom");
        assert_eq!(definition.proof_status, ProofStatus::DerivedProved);
        assert!(
            definition.elaborated_value.is_some(),
            "{name} must have a kernel-checked proof"
        );
        assert!(
            crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
            "{name} must have empty actual transitive axiom closure"
        );
    }

    #[test]
    fn schematic_lookup_closedness_and_loose_bvar_controls_are_checked() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for name in [
                "kdecl_type_at_closed",
                "kdecl_type_at_psubst_closed",
                "kdecl_type_at_lift_closed",
            ] {
                assert_checked_without_axioms(&spec, name);
            }
            spec.add_recursive_def(
                r"def decl_closed_test_type : Level -> KExpr := fun (u : Level) => KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)",
                "Model fixture: closed binder with a universe parameter, or a genuinely loose bound variable.",
            )
            .expect("lookup closedness fixture");
            spec.add_recursive_def(
                r"def decl_closed_test_sig : KConstSig := KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name)) (decl_closed_test_type (Level.param Name.anonymous))",
                "Model fixture: closed binder with a universe parameter, or a genuinely loose bound variable.",
            )
            .expect("lookup closedness fixture");
            spec.add_recursive_def(
                r"def decl_closed_test_env : KDeclEnv := fun (_n : Name) => OptionType.some KConstSig decl_closed_test_sig",
                "Model fixture: closed binder with a universe parameter, or a genuinely loose bound variable.",
            )
            .expect("lookup closedness fixture");
            spec.add_recursive_def(
                r"def decl_closed_test_loose_sig : KConstSig := KConstSig.mk (ListType.nil Name) (KExpr.bvar Nat.zero)",
                "Model fixture: closed binder with a universe parameter, or a genuinely loose bound variable.",
            )
            .expect("lookup closedness fixture");
            spec.add_recursive_def(
                r"def decl_closed_test_loose_env : KDeclEnv := fun (_n : Name) => OptionType.some KConstSig decl_closed_test_loose_sig",
                "Model fixture: closed binder with a universe parameter, or a genuinely loose bound variable.",
            )
            .expect("lookup closedness fixture");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_stored",
                r"forall (sig : KConstSig), Eq (OptionType KConstSig) (decl_closed_test_env Name.anonymous) (OptionType.some KConstSig sig) -> is_closed_at (kconst_type sig) Nat.zero",
                r"fun (sig : KConstSig)
    (h : Eq (OptionType KConstSig) (decl_closed_test_env Name.anonymous) (OptionType.some KConstSig sig)) =>
  Eq.substType KConstSig (fun (s : KConstSig) => is_closed_at (kconst_type s) Nat.zero)
    decl_closed_test_sig sig (option_some_inj KConstSig decl_closed_test_sig sig h)
    (is_closed_at.lam (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero) Nat.zero
      (is_closed_at.sort (Level.param Name.anonymous) Nat.zero)
      (is_closed_at.bvar Nat.zero (Nat.succ Nat.zero) (Lt.zero_lt_succ Nat.zero)))",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_stored");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_result",
                r"forall (u : Level), Eq (OptionType KExpr) (kdecl_type_at decl_closed_test_env Name.anonymous (ListType.cons Level u (ListType.nil Level))) (OptionType.some KExpr (decl_closed_test_type u))",
                r"fun (u : Level) => kdecl_type_at_intro decl_closed_test_env Name.anonymous decl_closed_test_sig (ListType.cons Level u (ListType.nil Level))
  (Eq.refl (OptionType KConstSig) (OptionType.some KConstSig decl_closed_test_sig)) (Eq.refl Nat (Nat.succ Nat.zero))",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_result");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_result_closed",
                r"forall (u : Level), is_closed_at (decl_closed_test_type u) Nat.zero",
                r"fun (u : Level) => kdecl_type_at_closed decl_closed_test_env Name.anonymous (ListType.cons Level u (ListType.nil Level)) (decl_closed_test_type u) decl_closed_test_stored (decl_closed_test_result u)",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_result_closed");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_result_psubst",
                r"forall (u : Level) (s : Nat -> KExpr), Eq KExpr (psubst s (decl_closed_test_type u)) (decl_closed_test_type u)",
                r"fun (u : Level) (s : Nat -> KExpr) => kdecl_type_at_psubst_closed decl_closed_test_env Name.anonymous (ListType.cons Level u (ListType.nil Level)) (decl_closed_test_type u) decl_closed_test_stored (decl_closed_test_result u) s",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_result_psubst");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_result_lift",
                r"forall (u : Level) (cutoff : Nat) (amount : Nat), Eq KExpr (lift_at (decl_closed_test_type u) cutoff amount) (decl_closed_test_type u)",
                r"fun (u : Level) (cutoff : Nat) (amount : Nat) => kdecl_type_at_lift_closed decl_closed_test_env Name.anonymous (ListType.cons Level u (ListType.nil Level)) (decl_closed_test_type u) decl_closed_test_stored (decl_closed_test_result u) cutoff amount",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_result_lift");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_zero",
                r"is_closed_at (decl_closed_test_type Level.zero) Nat.zero",
                r"decl_closed_test_result_closed Level.zero",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_zero");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_one",
                r"is_closed_at (decl_closed_test_type (Level.succ Level.zero)) Nat.zero",
                r"decl_closed_test_result_closed (Level.succ Level.zero)",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_one");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_loose_lookup",
                r"Eq (OptionType KExpr) (kdecl_type_at decl_closed_test_loose_env Name.anonymous (ListType.nil Level)) (OptionType.some KExpr (KExpr.bvar Nat.zero))",
                r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.bvar Nat.zero))",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_loose_lookup");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_loose_not_closed",
                r"is_closed_at (KExpr.bvar Nat.zero) Nat.zero -> Empty",
                r"fun (h : is_closed_at (KExpr.bvar Nat.zero) Nat.zero) =>
  nat_zero_ne_succ Nat.zero Empty
    (Eq.symm Nat (Nat.succ Nat.zero) Nat.zero
      (kexpr_bvar_inj (Nat.succ Nat.zero) Nat.zero
        (lift_closed_at_id (KExpr.bvar Nat.zero) Nat.zero h Nat.zero (Nat.succ Nat.zero) (le_zero_n Nat.zero))))",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_loose_not_closed");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_unqualified_result_closed_refuted",
                r"(forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr), Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T) -> is_closed_at T Nat.zero) -> Empty",
                r"fun (h : forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr), Eq (OptionType KExpr) (kdecl_type_at env n us) (OptionType.some KExpr T) -> is_closed_at T Nat.zero) => decl_closed_test_loose_not_closed (h decl_closed_test_loose_env Name.anonymous (ListType.nil Level) (KExpr.bvar Nat.zero) decl_closed_test_loose_lookup)",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(
                &spec,
                "decl_closed_test_unqualified_result_closed_refuted",
            );
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_loose_psubst_not_id",
                r"Eq KExpr (psubst (fun (_i : Nat) => KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero) -> Empty",
                r"fun (h : Eq KExpr (psubst (fun (_i : Nat) => KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) => nat_zero_ne_succ Nat.zero Empty (Eq.symm Nat (Nat.succ Nat.zero) Nat.zero (kexpr_bvar_inj (Nat.succ Nat.zero) Nat.zero h))",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_loose_psubst_not_id");
            lookup_closedness_theorem(
                &mut spec,
                "decl_closed_test_loose_lift_not_id",
                r"Eq KExpr (lift_at (KExpr.bvar Nat.zero) Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero) -> Empty",
                r"fun (h : Eq KExpr (lift_at (KExpr.bvar Nat.zero) Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) => nat_zero_ne_succ Nat.zero Empty (Eq.symm Nat (Nat.succ Nat.zero) Nat.zero (kexpr_bvar_inj (Nat.succ Nat.zero) Nat.zero h))",
                "Checked control: schematic closure suffices; successful lookup and correct arity alone do not.",
            )
            .expect("lookup closedness control");
            assert_checked_without_axioms(&spec, "decl_closed_test_loose_lift_not_id");
            assert!(lookup_closedness_theorem(
                &mut spec,
                "decl_closed_forged_loose_bvar_closed",
                "is_closed_at (KExpr.bvar Nat.zero) Nat.zero",
                "is_closed_at.bvar Nat.zero Nat.zero (Lt.zero_lt_succ Nat.zero)",
                "Negative control: successor-depth BVar closure does not establish top-level closure.",
            )
            .is_err());
            assert!(lookup_closedness_theorem(
                &mut spec,
                "decl_closed_forged_loose_psubst_identity",
                "Eq KExpr (psubst (fun (_i : Nat) => KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)",
                "Eq.refl KExpr (KExpr.bvar Nat.zero)",
                "Negative control: a successful lookup of a loose variable need not be substitution-invariant.",
            )
            .is_err());
        });
    }
}

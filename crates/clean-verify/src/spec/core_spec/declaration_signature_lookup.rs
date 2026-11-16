// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked introduction, refusal and CPS inversion for computed declaration lookup.
//!
//! The computation registers early in declaration_signatures. This later stage
//! reuses genuine Nat-equality reflection and OptionType no-confusion proofs;
//! no guard reflection, uninterpreted lookup, typing or source axiom is assumed.
//! Proof terms were checked against the exact exported dependency slice in
//! scratch/self-verification-declaration-lookup-2026-09-08.lean.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn lookup_theorem(
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
    /// Requires declaration_signatures, nat_eqb_eq, nat_eqb_refl,
    /// option_some_inj and option_none_ne_some_type. Safe immediately after
    /// add_snschema, without moving the reflection proof slice earlier.
    pub(super) fn add_declaration_signature_lookup(&mut self) -> Result<(), SpecError> {
        lookup_theorem(
            self,
            "kconst_arity_check_true",
            r"forall (sig : KConstSig) (us : ListType Level), kconst_arity sig us -> @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true",
            r"fun (sig : KConstSig) (us : ListType Level) (harity : kconst_arity sig us) =>
  @Eq.substType Nat (fun (arg_count : Nat) => @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) arg_count) Bool.true)
    (name_list_len (kconst_params sig)) (level_list_len us) harity (nat_eqb_refl (name_list_len (kconst_params sig)))",
            "Exact arity implies the computed Nat equality guard is true, using the existing checked nat_eqb_refl and equality transport.",
        )?;
        lookup_theorem(
            self,
            "kconst_arity_check_false",
            r"forall (sig : KConstSig) (us : ListType Level), (kconst_arity sig us -> Empty) -> @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false",
            r"fun (sig : KConstSig) (us : ListType Level) (hbad : kconst_arity sig us -> Empty) =>
  @Bool.rec
    (fun (b : Bool) => @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) b -> @Eq Bool b Bool.false)
    (fun (_hg : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false) => @Eq.refl Bool Bool.false)
    (fun (hg : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true) =>
      @Empty.rec (fun (_ : Empty) => @Eq Bool Bool.true Bool.false)
        (hbad (nat_eqb_eq (name_list_len (kconst_params sig)) (level_list_len us) hg)))
    (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)))",
            "A refuted exact-arity premise forces the computed guard to false. The true branch is ruled out by the existing proved nat_eqb_eq, not assumed Boolean reflection.",
        )?;
        lookup_theorem(
            self,
            "kdecl_type_at_intro",
            r"forall (env : KDeclEnv) (n : Name) (sig : KConstSig) (us : ListType Level), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) -> kconst_arity sig us -> @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr (kconst_inst_type sig us))",
            r"fun (env : KDeclEnv) (n : Name) (sig : KConstSig) (us : ListType Level) (hlookup : @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig)) (harity : kconst_arity sig us) =>
  @Eq.trans (OptionType KExpr) (kdecl_type_at env n us) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) (@OptionType.some KExpr (kconst_inst_type sig us))
    (@Eq.cong (OptionType KConstSig) (OptionType KExpr)
    (fun (found : OptionType KConstSig) => (@OptionType.rec KConstSig (fun (_found : OptionType KConstSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KConstSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)))) found))
    (env n) (@OptionType.some KConstSig sig) hlookup)
    (@Eq.cong Bool (OptionType KExpr) (fun (b : Bool) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) b))
      (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true (kconst_arity_check_true sig us harity))",
            "A real signature lookup and proved exact arity make the computed lookup return that signature's instantiated type.",
        )?;
        lookup_theorem(
            self,
            "kdecl_type_at_missing",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level), @Eq (OptionType KConstSig) (env n) (@OptionType.none KConstSig) -> @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.none KExpr)",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (hmissing : @Eq (OptionType KConstSig) (env n) (@OptionType.none KConstSig)) =>
  @Eq.cong (OptionType KConstSig) (OptionType KExpr)
    (fun (found : OptionType KConstSig) => (@OptionType.rec KConstSig (fun (_found : OptionType KConstSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KConstSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)))) found))
    (env n) (@OptionType.none KConstSig) hmissing",
            "Missing-name lookup returns none at every universe argument list.",
        )?;
        lookup_theorem(
            self,
            "kdecl_type_at_wrong_arity",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (sig : KConstSig), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) -> (kconst_arity sig us -> Empty) -> @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.none KExpr)",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (sig : KConstSig) (hlookup : @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig)) (hbad : kconst_arity sig us -> Empty) =>
  @Eq.trans (OptionType KExpr) (kdecl_type_at env n us) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) (@OptionType.none KExpr)
    (@Eq.cong (OptionType KConstSig) (OptionType KExpr)
    (fun (found : OptionType KConstSig) => (@OptionType.rec KConstSig (fun (_found : OptionType KConstSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KConstSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)))) found))
    (env n) (@OptionType.some KConstSig sig) hlookup)
    (@Eq.cong Bool (OptionType KExpr) (fun (b : Bool) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) b))
      (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false (kconst_arity_check_false sig us hbad))",
            "An existing declaration with provably wrong arity returns none; the raw instantiation default cannot escape the guard.",
        )?;
        lookup_theorem(
            self,
            "kdecl_type_at_some_inv",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr), @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr T) ->
    forall (C : Type),
      (forall (sig : KConstSig), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
        kconst_arity sig us -> @Eq KExpr T (kconst_inst_type sig us) -> C) -> C",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr)
    (h : @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr T))
    (C : Type)
    (k : forall (sig : KConstSig), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
      kconst_arity sig us -> @Eq KExpr T (kconst_inst_type sig us) -> C) =>
  @OptionType.rec KConstSig
    (fun (found : OptionType KConstSig) =>
      @Eq (OptionType KConstSig) (env n) found ->
      @Eq (OptionType KExpr) (@OptionType.rec KConstSig (fun (_found : OptionType KConstSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KConstSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)))) found) (@OptionType.some KExpr T) -> C)
    (fun (_hlookup : @Eq (OptionType KConstSig) (env n) (@OptionType.none KConstSig))
      (hresult : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
      option_none_ne_some_type KExpr T C hresult)
    (fun (sig : KConstSig) (hlookup : @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig))
      (hresult : @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) (@OptionType.some KExpr T)) =>
      @Bool.rec
        (fun (b : Bool) => @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) b ->
          @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) b) (@OptionType.some KExpr T) -> C)
        (fun (_hg : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false)
          (hr : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
          option_none_ne_some_type KExpr T C hr)
        (fun (hg : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
          (hr : @Eq (OptionType KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (@OptionType.some KExpr T)) =>
          k sig hlookup (nat_eqb_eq (name_list_len (kconst_params sig)) (level_list_len us) hg)
            (@Eq.symm KExpr (kconst_inst_type sig us) T (option_some_inj KExpr (kconst_inst_type sig us) T hr)))
        (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) hresult)
    (env n) (@Eq.refl (OptionType KConstSig) (env n)) h",
            "Type-valued CPS inversion of actual computed lookup: exposes the stored signature, its exact lookup equation, checked arity, and equality of the returned type with genuine instantiation. Missing and false-guard arms are impossible by proved OptionType no-confusion.",
        )?;
        lookup_theorem(
            self,
            "kdecl_type_at_some_inv_prop",
            r"forall (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr), @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr T) ->
    forall (C : Prop),
      (forall (sig : KConstSig), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
        kconst_arity sig us -> @Eq KExpr T (kconst_inst_type sig us) -> C) -> C",
            r"fun (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr)
    (h : @Eq (OptionType KExpr) (kdecl_type_at env n us) (@OptionType.some KExpr T))
    (C : Prop)
    (k : forall (sig : KConstSig), @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) ->
      kconst_arity sig us -> @Eq KExpr T (kconst_inst_type sig us) -> C) =>
  @OptionType.rec KConstSig
    (fun (found : OptionType KConstSig) =>
      @Eq (OptionType KConstSig) (env n) found ->
      @Eq (OptionType KExpr) (@OptionType.rec KConstSig (fun (_found : OptionType KConstSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KConstSig) => (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)))) found) (@OptionType.some KExpr T) -> C)
    (fun (_hlookup : @Eq (OptionType KConstSig) (env n) (@OptionType.none KConstSig))
      (hresult : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
      @Empty.rec (fun (_ : Empty) => C) (option_none_ne_some_type KExpr T Empty hresult))
    (fun (sig : KConstSig) (hlookup : @Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig))
      (hresult : @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) (@OptionType.some KExpr T)) =>
      @Bool.rec
        (fun (b : Bool) => @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) b ->
          @Eq (OptionType KExpr) (@Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) b) (@OptionType.some KExpr T) -> C)
        (fun (_hg : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false)
          (hr : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr T)) =>
          @Empty.rec (fun (_ : Empty) => C) (option_none_ne_some_type KExpr T Empty hr))
        (fun (hg : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
          (hr : @Eq (OptionType KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (@OptionType.some KExpr T)) =>
          k sig hlookup (nat_eqb_eq (name_list_len (kconst_params sig)) (level_list_len us) hg)
            (@Eq.symm KExpr (kconst_inst_type sig us) T (option_some_inj KExpr (kconst_inst_type sig us) T hr)))
        (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) hresult)
    (env n) (@Eq.refl (OptionType KConstSig) (env n)) h",
            "Prop-valued companion of the CPS inverter. Exposes the same actual signature, lookup, arity, and returned-type equation; impossible arms eliminate a proved Empty into the proposition.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::lookup_theorem;
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

    fn assert_body_type_mismatch(name: &str, error: &crate::spec::SpecError) {
        let crate::spec::SpecError::TypeError(detail) = error else {
            panic!("{name}: expected kernel body type mismatch, got {error:?}");
        };
        assert!(detail.starts_with(&format!("add_decl {name}:")), "{detail}");
        assert!(detail.contains("Type mismatch"), "{detail}");
    }

    #[test]
    fn declaration_lookup_graph_proofs_and_controls_have_empty_axiom_closure() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for name in [
                "kconst_arity_check_true",
                "kconst_arity_check_false",
                "kdecl_type_at_intro",
                "kdecl_type_at_missing",
                "kdecl_type_at_wrong_arity",
                "kdecl_type_at_some_inv",
                "kdecl_type_at_some_inv_prop",
            ] {
                assert_checked_without_axioms(&spec, name);
            }
            spec.add_recursive_def(
                r"def decl_lookup_test_sig : KConstSig := KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.succ (Level.param Name.anonymous)))",
                "Concrete model fixture for the declaration-lookup proof controls.",
            )
            .expect("lookup fixture");
            spec.add_recursive_def(
                r"def decl_lookup_test_env : KDeclEnv := fun (_n : Name) => @OptionType.some KConstSig decl_lookup_test_sig",
                "Concrete model fixture for the declaration-lookup proof controls.",
            )
            .expect("lookup fixture");
            spec.add_recursive_def(
                r"def decl_lookup_test_us_zero : ListType Level := @ListType.cons Level Level.zero (@ListType.nil Level)",
                "Concrete model fixture for the declaration-lookup proof controls.",
            )
            .expect("lookup fixture");
            spec.add_recursive_def(
                r"def decl_lookup_test_us_one : ListType Level := @ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)",
                "Concrete model fixture for the declaration-lookup proof controls.",
            )
            .expect("lookup fixture");
            spec.add_inductive(
                r"inductive DeclarationLookupEvidence (env : KDeclEnv) (n : Name) (us : ListType Level) (T : KExpr) : Type
| intro : forall (sig : KConstSig), Eq (OptionType KConstSig) (env n) (@OptionType.some KConstSig sig) -> kconst_arity sig us -> Eq KExpr T (kconst_inst_type sig us) -> DeclarationLookupEvidence env n us T",
                "Type-valued control records the signature and all three equations recovered by the generic inverter.",
            )
            .expect("lookup evidence carrier");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_all_universes",
                r"forall (u : Level), Eq (OptionType KExpr) (kdecl_type_at decl_lookup_test_env Name.anonymous (@ListType.cons Level u (@ListType.nil Level))) (@OptionType.some KExpr (KExpr.sort (Level.succ u)))",
                r"fun (u : Level) => kdecl_type_at_intro decl_lookup_test_env Name.anonymous decl_lookup_test_sig (@ListType.cons Level u (@ListType.nil Level)) (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig decl_lookup_test_sig)) (@Eq.refl Nat (Nat.succ Nat.zero))",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_all_universes");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_intro_zero",
                r"Eq (OptionType KExpr) (kdecl_type_at decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
                r"kdecl_type_at_intro decl_lookup_test_env Name.anonymous decl_lookup_test_sig decl_lookup_test_us_zero
  (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig decl_lookup_test_sig))
  (@Eq.refl Nat (Nat.succ Nat.zero))",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_intro_zero");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_type_inv_zero",
                r"DeclarationLookupEvidence decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero (KExpr.sort (Level.succ Level.zero))",
                r"kdecl_type_at_some_inv decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero (KExpr.sort (Level.succ Level.zero)) decl_lookup_test_intro_zero (DeclarationLookupEvidence decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero (KExpr.sort (Level.succ Level.zero)))
  (fun (sig : KConstSig) (hl : Eq (OptionType KConstSig) (decl_lookup_test_env Name.anonymous) (@OptionType.some KConstSig sig))
    (ha : kconst_arity sig decl_lookup_test_us_zero) (ht : Eq KExpr (KExpr.sort (Level.succ Level.zero)) (kconst_inst_type sig decl_lookup_test_us_zero)) =>
    @DeclarationLookupEvidence.intro decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero (KExpr.sort (Level.succ Level.zero)) sig hl ha ht)",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_type_inv_zero");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_prop_inv_zero",
                r"Eq KExpr (KExpr.sort (Level.succ Level.zero)) (kconst_inst_type decl_lookup_test_sig decl_lookup_test_us_zero)",
                r"kdecl_type_at_some_inv_prop decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero (KExpr.sort (Level.succ Level.zero)) decl_lookup_test_intro_zero (Eq KExpr (KExpr.sort (Level.succ Level.zero)) (kconst_inst_type decl_lookup_test_sig decl_lookup_test_us_zero))
  (fun (sig : KConstSig) (hl : Eq (OptionType KConstSig) (decl_lookup_test_env Name.anonymous) (@OptionType.some KConstSig sig))
    (_ha : kconst_arity sig decl_lookup_test_us_zero) (ht : Eq KExpr (KExpr.sort (Level.succ Level.zero)) (kconst_inst_type sig decl_lookup_test_us_zero)) =>
    Eq.trans KExpr (KExpr.sort (Level.succ Level.zero)) (kconst_inst_type sig decl_lookup_test_us_zero) (kconst_inst_type decl_lookup_test_sig decl_lookup_test_us_zero) ht
      (Eq.cong KConstSig KExpr (fun (s : KConstSig) => kconst_inst_type s decl_lookup_test_us_zero) sig decl_lookup_test_sig
        (Eq.symm KConstSig decl_lookup_test_sig sig
          (option_some_inj KConstSig decl_lookup_test_sig sig hl))))",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_prop_inv_zero");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_intro_one",
                r"Eq (OptionType KExpr) (kdecl_type_at decl_lookup_test_env Name.anonymous decl_lookup_test_us_one) (@OptionType.some KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))))",
                r"kdecl_type_at_intro decl_lookup_test_env Name.anonymous decl_lookup_test_sig decl_lookup_test_us_one
  (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig decl_lookup_test_sig))
  (@Eq.refl Nat (Nat.succ Nat.zero))",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_intro_one");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_type_inv_one",
                r"DeclarationLookupEvidence decl_lookup_test_env Name.anonymous decl_lookup_test_us_one (KExpr.sort (Level.succ (Level.succ Level.zero)))",
                r"kdecl_type_at_some_inv decl_lookup_test_env Name.anonymous decl_lookup_test_us_one (KExpr.sort (Level.succ (Level.succ Level.zero))) decl_lookup_test_intro_one (DeclarationLookupEvidence decl_lookup_test_env Name.anonymous decl_lookup_test_us_one (KExpr.sort (Level.succ (Level.succ Level.zero))))
  (fun (sig : KConstSig) (hl : Eq (OptionType KConstSig) (decl_lookup_test_env Name.anonymous) (@OptionType.some KConstSig sig))
    (ha : kconst_arity sig decl_lookup_test_us_one) (ht : Eq KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (kconst_inst_type sig decl_lookup_test_us_one)) =>
    @DeclarationLookupEvidence.intro decl_lookup_test_env Name.anonymous decl_lookup_test_us_one (KExpr.sort (Level.succ (Level.succ Level.zero))) sig hl ha ht)",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_type_inv_one");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_prop_inv_one",
                r"Eq KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (kconst_inst_type decl_lookup_test_sig decl_lookup_test_us_one)",
                r"kdecl_type_at_some_inv_prop decl_lookup_test_env Name.anonymous decl_lookup_test_us_one (KExpr.sort (Level.succ (Level.succ Level.zero))) decl_lookup_test_intro_one (Eq KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (kconst_inst_type decl_lookup_test_sig decl_lookup_test_us_one))
  (fun (sig : KConstSig) (hl : Eq (OptionType KConstSig) (decl_lookup_test_env Name.anonymous) (@OptionType.some KConstSig sig))
    (_ha : kconst_arity sig decl_lookup_test_us_one) (ht : Eq KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (kconst_inst_type sig decl_lookup_test_us_one)) =>
    Eq.trans KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (kconst_inst_type sig decl_lookup_test_us_one) (kconst_inst_type decl_lookup_test_sig decl_lookup_test_us_one) ht
      (Eq.cong KConstSig KExpr (fun (s : KConstSig) => kconst_inst_type s decl_lookup_test_us_one) sig decl_lookup_test_sig
        (Eq.symm KConstSig decl_lookup_test_sig sig
          (option_some_inj KConstSig decl_lookup_test_sig sig hl))))",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_prop_inv_one");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_missing_name",
                r"Eq (OptionType KExpr) (kdecl_type_at (fun (_n : Name) => @OptionType.none KConstSig) Name.anonymous decl_lookup_test_us_one) (@OptionType.none KExpr)",
                r"kdecl_type_at_missing (fun (_n : Name) => @OptionType.none KConstSig) Name.anonymous decl_lookup_test_us_one (@Eq.refl (OptionType KConstSig) (@OptionType.none KConstSig))",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_missing_name");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_missing_arity",
                r"kconst_arity decl_lookup_test_sig (@ListType.nil Level) -> Empty",
                r"fun (h : kconst_arity decl_lookup_test_sig (@ListType.nil Level)) => Eq.substType Nat (fun (n : Nat) => @Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat) n) (Nat.succ Nat.zero) Nat.zero h Nat.zero",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_missing_arity");
            lookup_theorem(
                &mut spec,
                "decl_lookup_test_wrong_arity",
                r"Eq (OptionType KExpr) (kdecl_type_at decl_lookup_test_env Name.anonymous (@ListType.nil Level)) (@OptionType.none KExpr)",
                r"kdecl_type_at_wrong_arity decl_lookup_test_env Name.anonymous (@ListType.nil Level) decl_lookup_test_sig (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig decl_lookup_test_sig)) decl_lookup_test_missing_arity",
                "Non-vacuity control using the registered general lookup theorem.",
            )
            .expect("checked lookup control");
            assert_checked_without_axioms(&spec, "decl_lookup_test_wrong_arity");
            assert!(lookup_theorem(
                &mut spec,
                "decl_lookup_forged_guard_reflection",
                "Eq Bool (nat_eqb (Nat.succ Nat.zero) Nat.zero) Bool.true",
                "@Eq.refl Bool Bool.true",
                "Negative control: an unequal arity guard cannot be assumed true.",
            )
            .inspect_err(|error| assert_body_type_mismatch(
                "decl_lookup_forged_guard_reflection",
                error
            ))
            .is_err());
            assert!(lookup_theorem(
                &mut spec,
                "decl_lookup_forged_wrong_arity_return",
                "Eq (OptionType KExpr) (kdecl_type_at decl_lookup_test_env Name.anonymous (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
                "@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
                "Negative control: the raw missing-argument default is not a successful checked lookup.",
            )
            .inspect_err(|error| assert_body_type_mismatch("decl_lookup_forged_wrong_arity_return", error))
            .is_err());
            assert!(lookup_theorem(
                &mut spec,
                "decl_lookup_forged_wrong_type_return",
                "Eq (OptionType KExpr) (kdecl_type_at decl_lookup_test_env Name.anonymous decl_lookup_test_us_zero) (@OptionType.some KExpr (KExpr.sort Level.zero))",
                "@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))",
                "Negative control: successful lookup cannot substitute a wrong returned type.",
            )
            .inspect_err(|error| assert_body_type_mismatch("decl_lookup_forged_wrong_type_return", error))
            .is_err());
        });
    }
}

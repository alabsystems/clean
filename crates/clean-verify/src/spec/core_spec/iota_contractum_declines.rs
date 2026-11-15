// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Independently checked draft views of the shared iota tail's actual refusal.
//!
//! This module is deliberately unregistered pending its operational pre-pass
//! caller. It neither defines a second tail nor changes any reducer, environment,
//! budget verdict or typing rule. A tail refusal is a stuck branch, not proof of
//! missing recursor rules, and not pre-pass starvation.
//!
//! The fixed-layout, opaque-RHS scope and producer obligations of
//! iota_contractum.rs remain unchanged.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (
        r"def iota_contractum_at_none_inv (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (C : Prop)
 (declined : Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
   (OptionType.none KExpr))
 (short : Eq Bool (iota_fields_ok rule majorArgs) Bool.false -> C)
 (wrong_arity : Eq Bool (iota_fields_ok rule majorArgs) Bool.true ->
   Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false -> C) : C :=
 Bool.rec
  (fun (b : Bool) => Eq Bool (iota_fields_ok rule majorArgs) b ->
    Eq (OptionType KExpr)
      (Bool.rec (fun (_ : Bool) => OptionType KExpr)
        (OptionType.none KExpr) (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
     (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs))) b)
      (OptionType.none KExpr) -> C)
  (fun (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.false)
    (_none : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.none KExpr)) =>
    short fields)
  (fun (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.true)
    (after_fields : Eq (OptionType KExpr) (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
     (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs))) (OptionType.none KExpr)) =>
    Bool.rec
      (fun (b : Bool) => Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) b ->
        Eq (OptionType KExpr)
          (opt_bind KExpr KExpr
            (Bool.rec (fun (_ : Bool) => OptionType KExpr)
              (OptionType.none KExpr) (OptionType.some KExpr (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us)) b)
            (fun (rhs : KExpr) => OptionType.some KExpr
              (iota_contractum mta rule args majorArgs rhs)))
          (OptionType.none KExpr) -> C)
      (fun (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false)
        (_none : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.none KExpr)) =>
        wrong_arity fields arity)
      (fun (_arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.true)
        (bad : Eq (OptionType KExpr) (OptionType.some KExpr (iota_contractum mta rule args majorArgs (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us))) (OptionType.none KExpr)) =>
        Empty.rec (fun (_ : Empty) => C)
          (Eq.substType (OptionType KExpr)
            (fun (o : OptionType KExpr) =>
              OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type)
                Empty (fun (_ : KExpr) => Nat) o)
            (OptionType.some KExpr (iota_contractum mta rule args majorArgs (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us))) (OptionType.none KExpr) bad Nat.zero))
      (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) (Eq.refl Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us))) after_fields)
  (iota_fields_ok rule majorArgs)
  (Eq.refl Bool (iota_fields_ok rule majorArgs)) declined",
        "Prop elimination of an actual declined tail: short fields, or sufficient fields and wrong universe arity. The both-true branch contradicts Option constructors.",
    ),
    (
        r"def iota_contractum_at_none_inv_type (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (C : Type)
 (declined : Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
   (OptionType.none KExpr))
 (short : Eq Bool (iota_fields_ok rule majorArgs) Bool.false -> C)
 (wrong_arity : Eq Bool (iota_fields_ok rule majorArgs) Bool.true ->
   Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false -> C) : C :=
 Bool.rec
  (fun (b : Bool) => Eq Bool (iota_fields_ok rule majorArgs) b ->
    Eq (OptionType KExpr)
      (Bool.rec (fun (_ : Bool) => OptionType KExpr)
        (OptionType.none KExpr) (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
     (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs))) b)
      (OptionType.none KExpr) -> C)
  (fun (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.false)
    (_none : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.none KExpr)) =>
    short fields)
  (fun (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.true)
    (after_fields : Eq (OptionType KExpr) (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
     (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs))) (OptionType.none KExpr)) =>
    Bool.rec
      (fun (b : Bool) => Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) b ->
        Eq (OptionType KExpr)
          (opt_bind KExpr KExpr
            (Bool.rec (fun (_ : Bool) => OptionType KExpr)
              (OptionType.none KExpr) (OptionType.some KExpr (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us)) b)
            (fun (rhs : KExpr) => OptionType.some KExpr
              (iota_contractum mta rule args majorArgs rhs)))
          (OptionType.none KExpr) -> C)
      (fun (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false)
        (_none : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.none KExpr)) =>
        wrong_arity fields arity)
      (fun (_arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.true)
        (bad : Eq (OptionType KExpr) (OptionType.some KExpr (iota_contractum mta rule args majorArgs (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us))) (OptionType.none KExpr)) =>
        Empty.rec (fun (_ : Empty) => C)
          (Eq.substType (OptionType KExpr)
            (fun (o : OptionType KExpr) =>
              OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type)
                Empty (fun (_ : KExpr) => Nat) o)
            (OptionType.some KExpr (iota_contractum mta rule args majorArgs (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us))) (OptionType.none KExpr) bad Nat.zero))
      (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) (Eq.refl Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us))) after_fields)
  (iota_fields_ok rule majorArgs)
  (Eq.refl Bool (iota_fields_ok rule majorArgs)) declined",
        "Type-valued elimination of the same actual declined tail, retaining the true field guard in the arity branch.",
    ),
    (
        r"def iota_contractum_at_none_of_fields_false (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (short : Eq Bool (iota_fields_ok rule majorArgs) Bool.false) :
 Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
  (OptionType.none KExpr) :=
 Eq.cong Bool (OptionType KExpr)
  (fun (b : Bool) => Bool.rec (fun (_ : Bool) => OptionType KExpr)
    (OptionType.none KExpr) (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
     (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs))) b)
  (iota_fields_ok rule majorArgs) Bool.false short",
        "An actual false field guard refuses independently of universe arguments and all prefix/extra arguments.",
    ),
    (
        r"def iota_contractum_at_none_of_arity_false (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (wrong_arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false) :
 Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
  (OptionType.none KExpr) :=
 Bool.rec
  (fun (b : Bool) => Eq (OptionType KExpr)
    (Bool.rec (fun (_ : Bool) => OptionType KExpr)
      (OptionType.none KExpr) (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
     (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs))) b)
    (OptionType.none KExpr))
  (Eq.refl (OptionType KExpr) (OptionType.none KExpr))
  (Eq.cong Bool (OptionType KExpr)
    (fun (b : Bool) => opt_bind KExpr KExpr
      (Bool.rec (fun (_ : Bool) => OptionType KExpr)
        (OptionType.none KExpr) (OptionType.some KExpr (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us)) b)
      (fun (rhs : KExpr) => OptionType.some KExpr
        (iota_contractum mta rule args majorArgs rhs)))
    (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false wrong_arity)
  (iota_fields_ok rule majorArgs)",
        "An actual false arity guard refuses for either field Boolean; no field-success premise is required.",
    ),
    (
        r"def iota_contractum_at_none_arity_of_fields (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (declined : Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
   (OptionType.none KExpr))
 (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.true) :
 Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false :=
 iota_contractum_at_none_inv mta rule us args majorArgs
  (Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false) declined
  (fun (short : Eq Bool (iota_fields_ok rule majorArgs) Bool.false) =>
    Empty.rec (fun (_ : Empty) => Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false)
      (Eq.substType Bool
        (fun (b : Bool) => Bool.rec (fun (_ : Bool) => Type) Empty Nat b)
        Bool.true Bool.false
        (Eq.trans Bool Bool.true (iota_fields_ok rule majorArgs) Bool.false
          (Eq.symm Bool (iota_fields_ok rule majorArgs) Bool.true fields) short)
        Nat.zero))
  (fun (_fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.true)
    (wrong_arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us)) Bool.false) => wrong_arity)",
        "An actual successful field guard rules out the short-fields branch of the Prop none-inverter and exposes the false arity Boolean.",
    ),
    (
        r"def iota_tail_declines_missing_field : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)) iota_tail_fixture_args (ListType.nil KExpr))
 (OptionType.none KExpr) :=
 iota_contractum_at_none_of_fields_false iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)) iota_tail_fixture_args (ListType.nil KExpr) (Eq.refl Bool Bool.false)",
        "The existing root-tail missing field fixture calls the forward refusal theorem with its actual false Boolean guard.",
    ),
    (
        r"def iota_tail_declines_missing_field_case : Eq Nat
 (iota_contractum_at_none_inv_type iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)) iota_tail_fixture_args (ListType.nil KExpr) Nat
   iota_tail_declines_missing_field
   (fun (_short : Eq Bool (iota_fields_ok iota_tail_fixture_rule (ListType.nil KExpr)) Bool.false) => Nat.zero)
   (fun (_fields : Eq Bool (iota_fields_ok iota_tail_fixture_rule (ListType.nil KExpr)) Bool.true)
     (_arity : Eq Bool
       (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta)))
         (level_list_len (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)))) Bool.false) => Nat.succ Nat.zero))
 Nat.zero := Eq.refl Nat Nat.zero",
        "The Type-valued actual none-inverter computes the short-fields continuation on the missing field fixture.",
    ),
    (
        r"def iota_tail_declines_missing_universe : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.none KExpr) :=
 iota_contractum_at_none_of_arity_false iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields (Eq.refl Bool Bool.false)",
        "The existing root-tail missing universe fixture calls the forward refusal theorem with its actual false Boolean guard.",
    ),
    (
        r"def iota_tail_declines_missing_universe_case : Eq Nat
 (iota_contractum_at_none_inv_type iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields Nat
   iota_tail_declines_missing_universe
   (fun (_short : Eq Bool (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.false) => Nat.zero)
   (fun (_fields : Eq Bool (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.true)
     (_arity : Eq Bool
       (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta)))
         (level_list_len (ListType.nil Level))) Bool.false) => Nat.succ Nat.zero))
 (Nat.succ Nat.zero) := Eq.refl Nat (Nat.succ Nat.zero)",
        "The Type-valued actual none-inverter computes the sufficient-fields/wrong-arity continuation on the missing universe fixture.",
    ),
    (
        r"def iota_tail_declines_missing_universe_arity : Eq Bool
 (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta)))
   (level_list_len (ListType.nil Level))) Bool.false :=
 iota_contractum_at_none_arity_of_fields iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields
  iota_tail_declines_missing_universe (Eq.refl Bool Bool.true)",
        "The Prop none-inverter derives the actual missing universe arity failure while retaining the computed successful field guard.",
    ),
    (
        r"def iota_tail_declines_extra_universe : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))) iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.none KExpr) :=
 iota_contractum_at_none_of_arity_false iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))) iota_tail_fixture_args iota_tail_fixture_fields (Eq.refl Bool Bool.false)",
        "The existing root-tail extra universe fixture calls the forward refusal theorem with its actual false Boolean guard.",
    ),
    (
        r"def iota_tail_declines_extra_universe_case : Eq Nat
 (iota_contractum_at_none_inv_type iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))) iota_tail_fixture_args iota_tail_fixture_fields Nat
   iota_tail_declines_extra_universe
   (fun (_short : Eq Bool (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.false) => Nat.zero)
   (fun (_fields : Eq Bool (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.true)
     (_arity : Eq Bool
       (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta)))
         (level_list_len (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))))) Bool.false) => Nat.succ Nat.zero))
 (Nat.succ Nat.zero) := Eq.refl Nat (Nat.succ Nat.zero)",
        "The Type-valued actual none-inverter computes the sufficient-fields/wrong-arity continuation on the extra universe fixture.",
    ),
    (
        r"def iota_tail_declines_extra_universe_arity : Eq Bool
 (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta)))
   (level_list_len (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))))) Bool.false :=
 iota_contractum_at_none_arity_of_fields iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))) iota_tail_fixture_args iota_tail_fixture_fields
  iota_tail_declines_extra_universe (Eq.refl Bool Bool.true)",
        "The Prop none-inverter derives the actual extra universe arity failure while retaining the computed successful field guard.",
    ),
];

impl Specification {
    /// General views precede the actual stuck-prepass consumers.
    pub(super) fn add_iota_contractum_declines(&mut self) -> Result<(), SpecError> {
        for (source, description) in &DECLARATIONS[..5] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }

    /// Concrete refusal callers require the late shared-tail fixtures.
    pub(super) fn add_iota_contractum_decline_controls(&mut self) -> Result<(), SpecError> {
        for (source, description) in &DECLARATIONS[5..] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::DECLARATIONS;
    use crate::spec::Specification;

    const PROOF_ROOTS: &[&str] = &[
        "iota_contractum_at_none_inv",
        "iota_contractum_at_none_inv_type",
        "iota_contractum_at_none_of_fields_false",
        "iota_contractum_at_none_of_arity_false",
        "iota_contractum_at_none_arity_of_fields",
        "iota_tail_declines_missing_field",
        "iota_tail_declines_missing_field_case",
        "iota_tail_declines_missing_universe",
        "iota_tail_declines_missing_universe_case",
        "iota_tail_declines_missing_universe_arity",
        "iota_tail_declines_extra_universe",
        "iota_tail_declines_extra_universe_case",
        "iota_tail_declines_extra_universe_arity",
    ];

    const NEGATIVE_CONTROLS: &[&str] = &[
        r"def iota_tail_declines_forged_missing_field : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)) iota_tail_fixture_args (ListType.nil KExpr))
 (OptionType.some KExpr iota_tail_fixture_result) :=
 iota_tail_declines_missing_field",
        r"def iota_tail_declines_forged_missing_universe : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.some KExpr iota_tail_fixture_result) :=
 iota_tail_declines_missing_universe",
        r"def iota_tail_declines_forged_extra_universe : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))) iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.some KExpr iota_tail_fixture_result) :=
 iota_tail_declines_extra_universe",
    ];

    #[test]
    fn iota_contractum_declines_sources_parse() {
        for (source, _) in DECLARATIONS {
            crate::test_utils::parse_check(source).expect("refusal declaration parses");
        }
        for source in NEGATIVE_CONTROLS {
            crate::test_utils::parse_check(source).expect("malformed-success control parses");
        }
    }

    #[test]
    fn iota_contractum_declines_and_both_views_are_checked() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_red_env_reflection_seed()
                .expect("artifact-independent early operations");
            if !spec.definitions().contains_key("iota_contractum_at") {
                spec.add_iota_contractum()
                    .expect("actual shared tail checks");
            }
            if !spec.definitions().contains_key("iota_tail_fixture_accepts") {
                spec.add_iota_contractum_controls()
                    .expect("actual root-tail fixtures check");
            }
            spec.add_iota_contractum_declines()
                .expect("actual refusal views check");
            spec.add_iota_contractum_decline_controls()
                .expect("actual refusal controls check");
            for name in PROOF_ROOTS {
                let definition = spec
                    .definitions()
                    .get(*name)
                    .unwrap_or_else(|| panic!("checked declaration {name}"));
                assert!(!definition.is_axiom, "{name}");
                assert!(definition.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
            for source in NEGATIVE_CONTROLS {
                assert!(spec
                    .add_recursive_def(
                        source,
                        "Reject a forged successful tail after actual refusal."
                    )
                    .is_err());
            }
        });
    }
}

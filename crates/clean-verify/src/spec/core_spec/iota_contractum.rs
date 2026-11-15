// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared guarded tail for the direct migration of the existing iota operators.
//!
//! This is the fixed MajorAfterMinors, opaque-RHS computation. The actual source
//! lambda branch must be established before metadata erasure by the producer.
//! It does not cover alternate layouts, fallback, K/native/cubical branches,
//! recursor admission, or production smart-universe substitution.
//! The shared tail, graph proofs and controls are registered. The existing raw
//! and pre-pass operators now call this tail with their actual head universes.
//! Rust execution attachment and the excluded source branches above remain
//! separate obligations.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const OPERATIONS: &[(&str, &str)] = &[
    (
        r"def iota_prefix_count (mta : RecMeta) : Nat :=
 Nat.add (Nat.add (recmeta_num_params mta) (recmeta_num_motives mta))
  (recmeta_num_minors mta)",
        "The standard-layout parameter/motive/minor prefix length.",
    ),
    (
        r"def iota_major_index (mta : RecMeta) : Nat :=
 Nat.add (iota_prefix_count mta) (recmeta_num_indices mta)",
        "The actual major position for the fixed MajorAfterMinors layout.",
    ),
    (
        r"def iota_fields_ok (rule : RecRule) (majorArgs : ListType KExpr) : Bool :=
 nat_eqb (Nat.sub (recrule_num_fields rule) (list_length majorArgs)) Nat.zero",
        "Reject a constructor spine shorter than the rule's field count before truncated subtraction selects its tail.",
    ),
    (
        r"def iota_contractum (mta : RecMeta) (rule : RecRule)
 (args : ListType KExpr) (majorArgs : ListType KExpr) (rhs : KExpr) : KExpr :=
 apply_spine (list_drop (Nat.succ (iota_major_index mta)) args)
  (apply_spine
    (list_drop (Nat.sub (list_length majorArgs) (recrule_num_fields rule)) majorArgs)
    (apply_spine (list_take (iota_prefix_count mta) args) rhs))",
        "Apply the actual standard-layout prefix, last constructor fields, and extra arguments to the supplied RHS, in source order.",
    ),
    (
        r"def iota_contractum_at (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr) : OptionType KExpr :=
 Bool.rec (fun (_fields : Bool) => OptionType KExpr)
  (OptionType.none KExpr)
  (opt_bind KExpr KExpr
    (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
    (fun (rhs : KExpr) => OptionType.some KExpr
      (iota_contractum mta rule args majorArgs rhs)))
  (iota_fields_ok rule majorArgs)",
        "Shared partial tail: first require enough constructor fields, then use the existing actual guarded schematic-RHS operation with the supplied head universes.",
    ),
];

/// Prop and Type continuations share exactly the same computation and proof.
fn guard_inversion_source(name: &str, sort: &str) -> String {
    let sig = "(recmeta_signature mta)";
    let rhs = "(recrule_rhs rule)";
    let arity = format!("(nat_eqb (name_list_len (kconst_params {sig})) (level_list_len us))");
    let value =
        format!("(iota_contractum mta rule args majorArgs (recursor_rhs_instance {sig} {rhs} us))");
    let inner = format!(
        "(opt_bind KExpr KExpr (recursor_rhs_at {sig} {rhs} us) (fun (body : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs body)))"
    );
    let impossible = r"Empty.rec (fun (_ : Empty) => C)
 (Eq.substType (OptionType KExpr)
   (fun (o : OptionType KExpr) =>
     OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type)
       Nat (fun (_ : KExpr) => Empty) o)
   (OptionType.none KExpr) (OptionType.some KExpr result) bad Nat.zero)";
    format!(
        r"def {name} (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (result : KExpr) (C : {sort})
 (accepted : Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
   (OptionType.some KExpr result))
 (consume : Eq Bool (iota_fields_ok rule majorArgs) Bool.true ->
   Eq Bool {arity} Bool.true -> Eq KExpr result {value} -> C) : C :=
 Bool.rec
  (fun (b : Bool) => Eq Bool (iota_fields_ok rule majorArgs) b ->
    Eq (OptionType KExpr)
      (Bool.rec (fun (_ : Bool) => OptionType KExpr) (OptionType.none KExpr) {inner} b)
      (OptionType.some KExpr result) -> C)
  (fun (_fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.false)
    (bad : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr result)) =>
    {impossible})
  (fun (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.true)
    (afterFields : Eq (OptionType KExpr) {inner} (OptionType.some KExpr result)) =>
    Bool.rec
      (fun (b : Bool) => Eq Bool {arity} b ->
        Eq (OptionType KExpr)
          (opt_bind KExpr KExpr
            (Bool.rec (fun (_ : Bool) => OptionType KExpr)
              (OptionType.none KExpr)
              (OptionType.some KExpr (recursor_rhs_instance {sig} {rhs} us)) b)
            (fun (body : KExpr) => OptionType.some KExpr
              (iota_contractum mta rule args majorArgs body)))
          (OptionType.some KExpr result) -> C)
      (fun (_arity : Eq Bool {arity} Bool.false)
        (bad : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr result)) =>
        {impossible})
      (fun (arity : Eq Bool {arity} Bool.true)
        (found : Eq (OptionType KExpr) (OptionType.some KExpr {value})
          (OptionType.some KExpr result)) =>
        consume fields arity
          (Eq.symm KExpr {value} result (option_some_inj KExpr {value} result found)))
      {arity} (Eq.refl Bool {arity}) afterFields)
  (iota_fields_ok rule majorArgs)
  (Eq.refl Bool (iota_fields_ok rule majorArgs)) accepted"
    )
}

const INTRO: &str = r"def iota_contractum_at_intro (mta : RecMeta) (rule : RecRule)
 (us : ListType Level) (args : ListType KExpr) (majorArgs : ListType KExpr)
 (fields : Eq Bool (iota_fields_ok rule majorArgs) Bool.true)
 (arity : Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature mta)))
   (level_list_len us)) Bool.true) :
 Eq (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
  (OptionType.some KExpr
    (iota_contractum mta rule args majorArgs
      (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us))) :=
 Eq.trans (OptionType KExpr) (iota_contractum_at mta rule us args majorArgs)
  (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
    (fun (rhs : KExpr) => OptionType.some KExpr (iota_contractum mta rule args majorArgs rhs)))
  (OptionType.some KExpr
    (iota_contractum mta rule args majorArgs
      (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us)))
  (Eq.cong Bool (OptionType KExpr)
    (fun (b : Bool) => Bool.rec (fun (_ : Bool) => OptionType KExpr)
      (OptionType.none KExpr)
      (opt_bind KExpr KExpr (recursor_rhs_at (recmeta_signature mta) (recrule_rhs rule) us)
        (fun (rhs : KExpr) => OptionType.some KExpr
          (iota_contractum mta rule args majorArgs rhs))) b)
    (iota_fields_ok rule majorArgs) Bool.true fields)
  (Eq.cong Bool (OptionType KExpr)
    (fun (b : Bool) => opt_bind KExpr KExpr
      (Bool.rec (fun (_ : Bool) => OptionType KExpr)
        (OptionType.none KExpr)
        (OptionType.some KExpr
          (recursor_rhs_instance (recmeta_signature mta) (recrule_rhs rule) us)) b)
      (fun (rhs : KExpr) => OptionType.some KExpr
        (iota_contractum mta rule args majorArgs rhs)))
    (nat_eqb (name_list_len (kconst_params (recmeta_signature mta))) (level_list_len us))
    Bool.true arity)";

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def iota_tail_fixture_level : Level := Level.succ (Level.param Name.anonymous)",
        "Nonzero supplied universe containing the stored parameter itself; repeated substitution changes it.",
    ),
    (
        r"def iota_tail_fixture_meta : RecMeta := RecMeta.mk (Nat.succ Nat.zero) Nat.zero Nat.zero Nat.zero Bool.true
 (KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name))
   (KExpr.sort (Level.param Name.anonymous))) Nat.zero",
        "Tail-only test metadata: one prefix argument, then major and extras. Its schematic signature is test data, not an admitted telescope.",
    ),
    (
        r"def iota_tail_fixture_rule : RecRule := RecRule.mk Name.anonymous (Nat.succ Nat.zero)
 (KExpr.lam (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero))",
        "One actual schematic lambda with one constructor field.",
    ),
    (
        r"def iota_tail_fixture_args : ListType KExpr :=
 ListType.cons KExpr (KExpr.sort Level.zero)
  (ListType.cons KExpr (KExpr.const Name.anonymous (ListType.nil Level))
    (ListType.cons KExpr (KExpr.sort (Level.succ (Level.succ Level.zero))) (ListType.nil KExpr)))",
        "Actual prefix/major/extra slots; head and major-constructor lookups are obligations of the surrounding operator, not this tail fixture.",
    ),
    (
        r"def iota_tail_fixture_fields : ListType KExpr :=
 ListType.cons KExpr (KExpr.bvar Nat.zero)
  (ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (ListType.nil KExpr))",
        "A constructor parameter followed by its field; the tail must retain only the last argument.",
    ),
    (
        r"def iota_tail_fixture_result : KExpr :=
 KExpr.app
  (KExpr.app
    (KExpr.app
      (KExpr.lam (KExpr.sort iota_tail_fixture_level) (KExpr.bvar Nat.zero))
      (KExpr.sort Level.zero))
    (KExpr.sort (Level.succ Level.zero)))
  (KExpr.sort (Level.succ (Level.succ Level.zero)))",
        "Independently spelled result: instantiate once, then prefix, last field, and extra in that order.",
    ),
    (
        r"def iota_tail_fixture_accepts : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))
   iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.some KExpr iota_tail_fixture_result) :=
 Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
        "The actual guarded computation produces the explicitly spelled nonzero, nonempty three-spine result.",
    ),
    (
        r"def iota_tail_fixture_intro : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))
   iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.some KExpr iota_tail_fixture_result) :=
 iota_contractum_at_intro iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))
  iota_tail_fixture_args iota_tail_fixture_fields
  (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)",
        "Actual reconstruction caller discharges both guards by computation and obtains the independently specified result.",
    ),
    (
        r"def iota_tail_fixture_invert : Eq Bool
 (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.true :=
 iota_contractum_at_guard_inv iota_tail_fixture_meta iota_tail_fixture_rule
  (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))
  iota_tail_fixture_args iota_tail_fixture_fields iota_tail_fixture_result
  (Eq Bool (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.true)
  iota_tail_fixture_accepts
  (fun (fields : Eq Bool (iota_fields_ok iota_tail_fixture_rule iota_tail_fixture_fields) Bool.true)
    (_arity : Eq Bool
      (nat_eqb (name_list_len (kconst_params (recmeta_signature iota_tail_fixture_meta)))
        (level_list_len (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)))) Bool.true)
    (_result : Eq KExpr iota_tail_fixture_result
      (iota_contractum iota_tail_fixture_meta iota_tail_fixture_rule
        iota_tail_fixture_args iota_tail_fixture_fields
        (recursor_rhs_instance (recmeta_signature iota_tail_fixture_meta)
          (recrule_rhs iota_tail_fixture_rule)
          (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))))) => fields)",
        "Actual successful-tail inversion yields the real field guard, retaining its arity and computed-output obligations.",
    ),
    (
        r"def iota_tail_fixture_missing_universe : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "The actual tail refuses a missing universe even with sufficient fields.",
    ),
    (
        r"def iota_tail_fixture_extra_universe : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level)))
   iota_tail_fixture_args iota_tail_fixture_fields)
 (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "The actual tail refuses extra universe arguments, not only missing ones.",
    ),
    (
        r"def iota_tail_fixture_missing_field : Eq (OptionType KExpr)
 (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule
   (ListType.cons Level iota_tail_fixture_level (ListType.nil Level))
   iota_tail_fixture_args (ListType.nil KExpr))
 (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "The actual tail refuses insufficient constructor fields even with exact universe arity.",
    ),
];

impl Specification {
    /// Called after the existing iota list/head operations, before iota_reduct.
    pub(super) fn add_iota_contractum(&mut self) -> Result<(), SpecError> {
        for (source, description) in OPERATIONS {
            self.add_recursive_def(source, description)?;
        }
        for (name, sort) in [
            ("iota_contractum_at_guard_inv", "Prop"),
            ("iota_contractum_at_guard_inv_type", "Type"),
        ] {
            self.add_recursive_def(
                &guard_inversion_source(name, sort),
                "Invert both actual tail guards and expose equality with the computed instantiated contractum. Neither false guard can produce a successful output.",
            )?;
        }
        self.add_recursive_def(
            INTRO,
            "The two actual true Boolean guards reconstruct the computed tail result; no output equation is assumed.",
        )?;
        Ok(())
    }

    pub(super) fn add_iota_contractum_controls(&mut self) -> Result<(), SpecError> {
        for (source, description) in CONTROLS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{guard_inversion_source, CONTROLS, INTRO, OPERATIONS};
    use crate::spec::Specification;

    const NEGATIVE_CONTROLS: &[&str] = &[
        r"def iota_tail_forged_missing_universe : Eq (OptionType KExpr) (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.nil Level) iota_tail_fixture_args iota_tail_fixture_fields) (OptionType.some KExpr iota_tail_fixture_result) := Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
        r"def iota_tail_forged_extra_universe : Eq (OptionType KExpr) (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.cons Level Level.zero (ListType.nil Level))) iota_tail_fixture_args iota_tail_fixture_fields) (OptionType.some KExpr iota_tail_fixture_result) := Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
        r"def iota_tail_forged_missing_field : Eq (OptionType KExpr) (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)) iota_tail_fixture_args (ListType.nil KExpr)) (OptionType.some KExpr iota_tail_fixture_result) := Eq.refl (OptionType KExpr) (OptionType.some KExpr iota_tail_fixture_result)",
        r"def iota_tail_forged_uninstantiated_rhs : Eq (OptionType KExpr) (iota_contractum_at iota_tail_fixture_meta iota_tail_fixture_rule (ListType.cons Level iota_tail_fixture_level (ListType.nil Level)) iota_tail_fixture_args iota_tail_fixture_fields) (OptionType.some KExpr (iota_contractum iota_tail_fixture_meta iota_tail_fixture_rule iota_tail_fixture_args iota_tail_fixture_fields (recrule_rhs iota_tail_fixture_rule))) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (iota_contractum iota_tail_fixture_meta iota_tail_fixture_rule iota_tail_fixture_args iota_tail_fixture_fields (recrule_rhs iota_tail_fixture_rule)))",
        r"def iota_tail_forged_argument_order : Eq KExpr iota_tail_fixture_result (KExpr.app (KExpr.app (KExpr.app (KExpr.lam (KExpr.sort iota_tail_fixture_level) (KExpr.bvar Nat.zero)) (KExpr.sort (Level.succ Level.zero))) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ (Level.succ Level.zero)))) := Eq.refl KExpr iota_tail_fixture_result",
    ];

    #[test]
    fn guarded_iota_tail_sources_parse() {
        for (source, _) in OPERATIONS.iter().chain(CONTROLS) {
            crate::test_utils::parse_check(source).expect("tail declaration parses");
        }
        for (name, sort) in [
            ("iota_contractum_at_guard_inv", "Prop"),
            ("iota_contractum_at_guard_inv_type", "Type"),
        ] {
            crate::test_utils::parse_check(&guard_inversion_source(name, sort))
                .expect("generated guard inversion parses");
        }
        crate::test_utils::parse_check(INTRO).expect("tail introduction parses");
        for source in NEGATIVE_CONTROLS {
            crate::test_utils::parse_check(source).expect("false control is syntactically valid");
        }
    }

    #[test]
    fn guarded_iota_tail_computation_and_refusals_are_checked() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_red_env_reflection_seed()
                .expect("artifact-independent early operations");
            if !spec.definitions().contains_key("iota_contractum_at") {
                spec.add_iota_contractum()
                    .expect("shared guarded tail checks");
            }
            spec.add_iota_contractum_controls()
                .expect("actual tail controls check");
            for name in [
                "iota_contractum_at_guard_inv",
                "iota_contractum_at_guard_inv_type",
                "iota_contractum_at_intro",
                "iota_tail_fixture_accepts",
                "iota_tail_fixture_intro",
                "iota_tail_fixture_invert",
                "iota_tail_fixture_missing_universe",
                "iota_tail_fixture_extra_universe",
                "iota_tail_fixture_missing_field",
            ] {
                let definition = spec.definitions().get(name).expect("checked declaration");
                assert!(!definition.is_axiom, "{name}");
                assert!(definition.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
            for source in NEGATIVE_CONTROLS {
                assert!(spec
                    .add_recursive_def(source, "Reject forged tail guard, RHS or argument order.")
                    .is_err());
            }
        });
    }
}

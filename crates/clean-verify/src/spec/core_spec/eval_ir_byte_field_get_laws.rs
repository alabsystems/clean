// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed payload-spine lookup derived from actual structural byte admission.
//!
//! The Byte constructor installs this derived law and checks its proof term
//! alongside the other value-bearing Byte additions.
//! Nominal field-type reflection, source/catalog authentication and execution
//! correspondence are separate obligations. No runtime check is removed.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_field_get_laws_v1(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            TYPED_SPINE_GET,
            "Generic typing of a successfully selected payload-spine lane, derived from exact input spine admission and both actual lookups. No source, catalog, or native authority.",
        )?;
        Ok(())
    }
}

const TYPED_SPINE_GET: &str = r"def ir_byte_field_spine_get_typed_v1 (ctx : IRByteContextV1) (spine : IRScalar) :
  forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar),
    @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types) Bool.true ->
    @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
    @Eq (IROption IRScalar) (ir_vals_get spine index) (@IROption.some IRScalar value) ->
    @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true :=
@IRScalar.rec
  (fun (s : IRScalar) => forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar),
    @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx s) types) Bool.true ->
    @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
    @Eq (IROption IRScalar) (ir_vals_get s index) (@IROption.some IRScalar value) ->
    @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
  (fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.undef_) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (b : Bool) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.bool_ b)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (n : Nat) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.int_ n)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (n : Nat) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.float_ n)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.unit_) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (n : Nat) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.ptr_ n)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.nullptr_) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (data metadata : Nat) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.fat_ data metadata)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (n : Nat) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.fnptr_ n)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (inner : IRScalar) (_ : forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar),
    @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx inner) types) Bool.true ->
    @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
    @Eq (IROption IRScalar) (ir_vals_get inner index) (@IROption.some IRScalar value) ->
    @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true) =>
    fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.aggv inner)) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar)
      (_ : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.vnil) types) Bool.true)
      (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
      (valueFound : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
      @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
        (ir_byte_field_option_none_some_false_v1 IRScalar value valueFound))
  (fun (head tail : IRScalar)
    (_ : forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar),
    @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx head) types) Bool.true ->
    @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
    @Eq (IROption IRScalar) (ir_vals_get head index) (@IROption.some IRScalar value) ->
    @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
    (tailIH : forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (value : IRScalar),
    @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) types) Bool.true ->
    @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
    @Eq (IROption IRScalar) (ir_vals_get tail index) (@IROption.some IRScalar value) ->
    @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true) =>
    fun (types : IRList IRTy) => @IRList.rec IRTy
      (fun (ts : IRList IRTy) => forall (index : Nat) (selected : IRTy) (value : IRScalar),
          @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.vcons head tail)) ts) Bool.true ->
          @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 ts index) (@IROption.some IRTy selected) ->
          @Eq (IROption IRScalar) (ir_vals_get (IRScalar.vcons head tail) index) (@IROption.some IRScalar value) ->
          @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
      (fun (index : Nat) (selected : IRTy) (value : IRScalar)
        (bad : @Eq Bool Bool.false Bool.true)
        (_ : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 (@IRList.nil IRTy) index)
          (@IROption.some IRTy selected))
        (_ : @Eq (IROption IRScalar) (ir_vals_get (IRScalar.vcons head tail) index)
          (@IROption.some IRScalar value)) =>
        @False.elim (@Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
          (ir_byte_world_false_true_v1 bad))
      (fun (ty : IRTy) (rest : IRList IRTy)
        (_ : forall (index : Nat) (selected : IRTy) (value : IRScalar),
          @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.vcons head tail)) rest) Bool.true ->
          @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 rest index) (@IROption.some IRTy selected) ->
          @Eq (IROption IRScalar) (ir_vals_get (IRScalar.vcons head tail) index) (@IROption.some IRScalar value) ->
          @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true) =>
        fun (index : Nat) => @Nat.rec
          (fun (position : Nat) => forall (selected : IRTy) (value : IRScalar),
            @Eq Bool (Bool.and (ir_byte_value_matches_v1 ctx ty head)
              (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest)) Bool.true ->
            @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 (@IRList.cons IRTy ty rest) position)
              (@IROption.some IRTy selected) ->
            @Eq (IROption IRScalar) (ir_vals_get (IRScalar.vcons head tail) position)
              (@IROption.some IRScalar value) ->
            @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
          (fun (selected : IRTy) (value : IRScalar)
            (inputTyped : @Eq Bool (Bool.and (ir_byte_value_matches_v1 ctx ty head)
              (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest)) Bool.true)
            (laneFound : @Eq (IROption IRTy) (@IROption.some IRTy ty) (@IROption.some IRTy selected))
            (valueFound : @Eq (IROption IRScalar) (@IROption.some IRScalar head) (@IROption.some IRScalar value)) =>
            @Eq.subst IRScalar
              (fun (v : IRScalar) => @Eq Bool (ir_byte_value_matches_v1 ctx selected v) Bool.true)
              head value (ir_byte_field_option_some_injective_v1 IRScalar head value valueFound)
              (@Eq.subst IRTy
                (fun (t : IRTy) => @Eq Bool (ir_byte_value_matches_v1 ctx t head) Bool.true)
                ty selected (ir_byte_field_option_some_injective_v1 IRTy ty selected laneFound)
                (ir_byte_world_and_left_v1 (ir_byte_value_matches_v1 ctx ty head)
                  (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest) inputTyped)))
          (fun (previous : Nat)
            (_ :  forall (selected : IRTy) (value : IRScalar),
            @Eq Bool (Bool.and (ir_byte_value_matches_v1 ctx ty head)
              (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest)) Bool.true ->
            @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 (@IRList.cons IRTy ty rest) previous)
              (@IROption.some IRTy selected) ->
            @Eq (IROption IRScalar) (ir_vals_get (IRScalar.vcons head tail) previous)
              (@IROption.some IRScalar value) ->
            @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true) =>
            fun (selected : IRTy) (value : IRScalar)
              (inputTyped : @Eq Bool (Bool.and (ir_byte_value_matches_v1 ctx ty head)
                (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest)) Bool.true)
              (laneFound : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 rest previous)
                (@IROption.some IRTy selected))
              (valueFound : @Eq (IROption IRScalar) (ir_vals_get tail previous)
                (@IROption.some IRScalar value)) =>
              tailIH rest previous selected value
                (ir_byte_world_and_right_v1 (ir_byte_value_matches_v1 ctx ty head)
                  (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest) inputTyped)
                laneFound valueFound) index) types)
  spine";

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    const ROOT: &str = "ir_byte_field_spine_get_typed_v1";
    const SPINE: &str =
        "IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.true) IRScalar.vnil)";
    const TYPES: &str =
        "@IRList.cons IRTy IRTy.unit_ (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))";

    fn specification() -> Specification {
        crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("actual registered public Byte vocabulary")
    }

    fn checked(spec: &Specification, name: &str) {
        let def = spec.get_definition(name).expect("value-bearing root");
        assert!(!def.is_axiom && def.elaborated_value.is_some());
        spec.verify_definition(name).expect("actual kernel check");
        let name = Name::from_string(name);
        assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
        assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
    }

    fn witness(index: &str, ty: &str, value: &str, name: &str) -> String {
        format!(
            "def {name} (ctx : IRByteContextV1) : \
             @Eq Bool (ir_byte_value_matches_v1 ctx ({ty}) ({value})) Bool.true := \
             {ROOT} ctx ({SPINE}) ({TYPES}) ({index}) ({ty}) ({value}) \
             (@Eq.refl Bool Bool.true) \
             (@Eq.refl (IROption IRTy) (@IROption.some IRTy ({ty}))) \
             (@Eq.refl (IROption IRScalar) (@IROption.some IRScalar ({value})))"
        )
    }

    fn rejected(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Unchanged-proof wrong selected lane type")
            .expect_err("wrong conclusion must not pass");
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn byte_field_spine_get_generic_law_is_checked_and_axiom_free() {
        crate::test_utils::run_with_stack(|| checked(&specification(), ROOT));
    }

    #[test]
    fn byte_field_spine_get_has_inhabited_head_and_successor_applications() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = specification();
            for (index, ty, value, name) in [
                (
                    "Nat.zero",
                    "IRTy.unit_",
                    "IRScalar.unit_",
                    "field_spine_get_head",
                ),
                (
                    "Nat.succ Nat.zero",
                    "IRTy.bool_",
                    "IRScalar.bool_ Bool.true",
                    "field_spine_get_tail",
                ),
            ] {
                let source = witness(index, ty, value, name);
                spec.add_recursive_def(&source, "Typed-spine lookup witness with computed inputs")
                    .unwrap_or_else(|error| panic!("{source}: {error}"));
                checked(&spec, name);
            }
        });
    }

    #[test]
    fn byte_field_spine_get_unchanged_proof_refuses_wrong_nominal_conclusion() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = specification();
            let positive = witness(
                "Nat.succ Nat.zero",
                "IRTy.bool_",
                "IRScalar.bool_ Bool.true",
                "field_spine_get_positive",
            );
            spec.add_recursive_def(&positive, "Inhabited typed successor lookup")
                .expect("correct selected type checks");
            checked(&spec, "field_spine_get_positive");
            let negative = positive
                .replacen(
                    "field_spine_get_positive",
                    "field_spine_get_wrong_nominal",
                    1,
                )
                .replacen(
                    "ir_byte_value_matches_v1 ctx (IRTy.bool_)",
                    "ir_byte_value_matches_v1 ctx (IRTy.unit_)",
                    1,
                );
            assert_eq!(
                positive.split_once(":=").unwrap().1,
                negative.split_once(":=").unwrap().1
            );
            rejected(&mut spec, "field_spine_get_wrong_nominal", &negative);
        });
    }
}

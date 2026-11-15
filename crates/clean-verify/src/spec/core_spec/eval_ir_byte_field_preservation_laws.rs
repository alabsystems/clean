// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive structural field proofs ported from independently checked Lean terms.
//!
//! The Byte constructor installs these declarations and checks their proof terms.
//! Runtime output checks and existing field APIs are unchanged. Catalog inputs
//! and nominal type metadata are not authenticated source/native certificates.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_field_preservation_laws_v1(&mut self) -> Result<(), SpecError> {
        for source in [
            ENUM_SPINE_SET_SUCC_INVARIANT,
            FIELD_TYPES_SET_WRITABLE_INVARIANT,
            AGGREGATE_SPINE_EQUATION,
            AGGREGATE_SELECTED_SPINE_EQUATION,
            INSERTED_VALUE_ADMISSION,
            SELECTED_INSERT_FROM_INPUTS,
        ] {
            self.add_recursive_def(
                source,
                "Generic structural field typing derived from actual admission/lookups. No output typing assumption, source authentication, or native authority; runtime guards retained.",
            )?;
        }
        Ok(())
    }
}

const ENUM_SPINE_SET_SUCC_INVARIANT: &str = r"def ir_byte_field_enum_spine_set_succ_invariant_v1 (ctx : IRByteContextV1)
  (id : Nat) (spine : IRScalar) (index : Nat) (value : IRScalar) :
  @Eq (IROption (IRList IRTy))
    (ir_byte_enum_spine_types_v1 ctx id (ir_vals_set spine (Nat.succ index) value))
    (ir_byte_enum_spine_types_v1 ctx id spine) :=
  @IRScalar.rec
    (fun original => @Eq (IROption (IRList IRTy))
      (ir_byte_enum_spine_types_v1 ctx id (ir_vals_set original (Nat.succ index) value))
      (ir_byte_enum_spine_types_v1 ctx id original))
    (@Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.undef_)))
    (fun (v0 : Bool) => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.bool_ v0)))
    (fun (v0 : Nat) => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.int_ v0)))
    (fun (v0 : Nat) => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.float_ v0)))
    (@Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.unit_)))
    (fun (v0 : Nat) => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.ptr_ v0)))
    (@Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.nullptr_)))
    (fun (v0 : Nat) (v1 : Nat) => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.fat_ v0 v1)))
    (fun (v0 : Nat) => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.fnptr_ v0)))
    (fun (v0 : IRScalar) _ => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.aggv v0)))
    (@Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.vnil)))
    (fun (v0 : IRScalar) (v1 : IRScalar) _ _ => @Eq.refl (IROption (IRList IRTy)) (ir_byte_enum_spine_types_v1 ctx id (IRScalar.vcons v0 v1)))
    spine";

const FIELD_TYPES_SET_WRITABLE_INVARIANT: &str = r"def ir_byte_field_types_set_writable_invariant_v1 (ctx : IRByteContextV1)
  (ty : IRTy) (spine : IRScalar) (index : Nat) (value : IRScalar)
  (writable : @Eq Bool (ir_byte_field_writable_v1 ty index) Bool.true) :
  @Eq (IROption (IRList IRTy))
    (ir_byte_field_types_v1 ctx ty (ir_vals_set spine index value))
    (ir_byte_field_types_v1 ctx ty spine) :=
  let invalid : forall (actual : IRTy),
    (forall (position : Nat), @Eq Bool (ir_byte_field_writable_v1 actual position) Bool.false) ->
    forall (position : Nat),
      @Eq Bool (ir_byte_field_writable_v1 actual position) Bool.true ->
      @Eq (IROption (IRList IRTy))
        (ir_byte_field_types_v1 ctx actual (ir_vals_set spine position value))
        (ir_byte_field_types_v1 ctx actual spine) :=
    fun actual refused position flag =>
      @False.elim
        (@Eq (IROption (IRList IRTy))
          (ir_byte_field_types_v1 ctx actual (ir_vals_set spine position value))
          (ir_byte_field_types_v1 ctx actual spine))
        (ir_byte_world_false_true_v1
          (@Eq.trans Bool Bool.false (ir_byte_field_writable_v1 actual position) Bool.true
            (@Eq.symm Bool (ir_byte_field_writable_v1 actual position) Bool.false (refused position)) flag))
  @IRTy.rec
    (fun actual =>
      forall (position : Nat),
        @Eq Bool (ir_byte_field_writable_v1 actual position) Bool.true ->
        @Eq (IROption (IRList IRTy))
          (ir_byte_field_types_v1 ctx actual (ir_vals_set spine position value))
          (ir_byte_field_types_v1 ctx actual spine))
    (invalid (IRTy.bool_) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : Nat) => invalid (IRTy.int_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : Nat) => invalid (IRTy.uint_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : Nat) => invalid (IRTy.float_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (invalid (IRTy.ptr_) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.ref_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.refmut_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.rawconst_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.rawmut_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.rc_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.fatptr_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (invalid (IRTy.unit_) (fun _ => @Eq.refl Bool Bool.false))
    (invalid (IRTy.never_) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : Nat) => invalid (IRTy.tuple_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) (a1 : Nat) _ => invalid (IRTy.array_ a0 a1) (fun _ => @Eq.refl Bool Bool.false))
    (fun id position _ => @Eq.refl (IROption (IRList IRTy)) (ir_byte_field_types_v1 ctx (IRTy.struct_ id) spine))
    (fun id position => @Nat.rec
      (fun lane => @Eq Bool (ir_byte_field_writable_v1 (IRTy.enum_ id) lane) Bool.true ->
        @Eq (IROption (IRList IRTy))
          (ir_byte_field_types_v1 ctx (IRTy.enum_ id) (ir_vals_set spine lane value))
          (ir_byte_field_types_v1 ctx (IRTy.enum_ id) spine))
      (fun impossible => @False.elim
        (@Eq (IROption (IRList IRTy))
          (ir_byte_field_types_v1 ctx (IRTy.enum_ id) (ir_vals_set spine Nat.zero value))
          (ir_byte_field_types_v1 ctx (IRTy.enum_ id) spine))
        (ir_byte_world_false_true_v1 impossible))
      (fun previous _ _ => ir_byte_field_enum_spine_set_succ_invariant_v1 ctx id spine previous value) position)
    (fun (a0 : Nat) => invalid (IRTy.func_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : Nat) => invalid (IRTy.usize_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (invalid (IRTy.fatstr_) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : IRTy) _ => invalid (IRTy.fatslice_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (fun (a0 : Nat) => invalid (IRTy.fatdyn_ a0) (fun _ => @Eq.refl Bool Bool.false))
    (invalid (IRTy.containerlen_) (fun _ => @Eq.refl Bool Bool.false))
    (invalid (IRTy.containervtable_) (fun _ => @Eq.refl Bool Bool.false))
    ty index writable

-- Explicit layout-option induction proves the map/rec fusion at a neutral lookup.";

const AGGREGATE_SPINE_EQUATION: &str = r"def ir_byte_field_aggregate_spine_equation_v1 (ctx : IRByteContextV1)
  (ty : IRTy) (spine : IRScalar) :
  @Eq Bool (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine))
    (@IROption.rec (IRList IRTy) (fun _ => Bool) Bool.false
      (fun types => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
      (ir_byte_field_types_v1 ctx ty spine)) :=
  @IRTy.rec
    (fun actual => @Eq Bool (ir_byte_value_matches_v1 ctx actual (IRScalar.aggv spine))
      (@IROption.rec (IRList IRTy) (fun _ => Bool) Bool.false
        (fun types => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
        (ir_byte_field_types_v1 ctx actual spine)))
    (@Eq.refl Bool Bool.false)
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (@Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (@Eq.refl Bool Bool.false)
    (@Eq.refl Bool Bool.false)
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) (a1 : Nat) _ => @Eq.refl Bool Bool.false)
    (fun id => @IROption.rec IRByteLayoutV1
      (fun found => @Eq Bool
        (@IROption.rec IRByteLayoutV1 (fun _ => Bool) Bool.false
          (fun layout => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) (ir_byte_layout_fields_v1 layout)) found)
        (@IROption.rec (IRList IRTy) (fun _ => Bool) Bool.false
          (fun types => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
          (@IROption.rec IRByteLayoutV1 (fun _ => (IROption (IRList IRTy)))
            (@IROption.none (IRList IRTy))
            (fun layout => @IROption.some (IRList IRTy) (ir_byte_layout_fields_v1 layout)) found)))
      (@Eq.refl Bool Bool.false)
      (fun layout => @Eq.refl Bool
        (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) (ir_byte_layout_fields_v1 layout)))
      (ir_byte_layout_v1 ctx (IRTy.struct_ id)))
    (fun id => @Eq.refl Bool
      (@IROption.rec (IRList IRTy) (fun _ => Bool) Bool.false
        (fun types => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
        (ir_byte_enum_spine_types_v1 ctx id spine)))
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (@Eq.refl Bool Bool.false)
    (fun (a0 : IRTy) _ => @Eq.refl Bool Bool.false)
    (fun (a0 : Nat) => @Eq.refl Bool Bool.false)
    (@Eq.refl Bool Bool.false)
    (@Eq.refl Bool Bool.false)
    ty";

const AGGREGATE_SELECTED_SPINE_EQUATION: &str = r"def ir_byte_field_aggregate_selected_spine_equation_v1 (ctx : IRByteContextV1)
  (ty : IRTy) (spine : IRScalar) (types : IRList IRTy)
  (typesFound : @Eq (IROption (IRList IRTy))
    (ir_byte_field_types_v1 ctx ty spine) (@IROption.some (IRList IRTy) types)) :
  @Eq Bool (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine))
    (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types) :=
  @Eq.trans Bool
    (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine))
    (@IROption.rec (IRList IRTy) (fun _ => Bool) Bool.false
      (fun rows => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) rows)
      (ir_byte_field_types_v1 ctx ty spine))
    (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
    (ir_byte_field_aggregate_spine_equation_v1 ctx ty spine)
    (ir_byte_case_some_v1 (IRList IRTy) Bool (ir_byte_field_types_v1 ctx ty spine) types Bool.false
      (fun rows => ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) rows)
      (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types) typesFound
      (@Eq.refl Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)))";

const INSERTED_VALUE_ADMISSION: &str = r"def ir_byte_field_inserted_value_admission_v1 (ctx : IRByteContextV1)
  (ty : IRTy) (spine : IRScalar) (index : Nat) (types : IRList IRTy)
  (selected : IRTy) (replacement : IRScalar)
  (inputAggregateValid : @Eq Bool (ir_byte_field_aggregate_valid_v1 ctx ty (IRScalar.aggv spine)) Bool.true)
  (writable : @Eq Bool (ir_byte_field_writable_v1 ty index) Bool.true)
  (typesFound : @Eq (IROption (IRList IRTy))
    (ir_byte_field_types_v1 ctx ty spine) (@IROption.some (IRList IRTy) types))
  (laneFound : @Eq (IROption IRTy)
    (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
  (replacementTyped : @Eq Bool (ir_byte_value_matches_v1 ctx selected replacement) Bool.true) :
  @Eq Bool (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv (ir_vals_set spine index replacement))) Bool.true :=
  let rootTyped : @Eq Bool (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine)) Bool.true :=
    ir_byte_world_and_right_v1
      (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))
      (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine))
      (ir_byte_world_and_right_v1
        (ir_byte_field_layouts_unique_v1 (ir_byte_context_layouts_v1 ctx))
        (Bool.and (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))
          (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine))) inputAggregateValid)
  let spineTyped : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types) Bool.true :=
    @Eq.trans Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
      (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine)) Bool.true
      (@Eq.symm Bool (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv spine))
        (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
        (ir_byte_field_aggregate_selected_spine_equation_v1 ctx ty spine types typesFound)) rootTyped
  let updatedTyped : @Eq Bool
    (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set spine index replacement)) types) Bool.true :=
    ir_byte_field_spine_set_typed_v1
      ctx spine types index selected replacement spineTyped laneFound replacementTyped
  let updatedTypes : @Eq (IROption (IRList IRTy))
    (ir_byte_field_types_v1 ctx ty (ir_vals_set spine index replacement))
    (@IROption.some (IRList IRTy) types) :=
    @Eq.trans (IROption (IRList IRTy))
      (ir_byte_field_types_v1 ctx ty (ir_vals_set spine index replacement))
      (ir_byte_field_types_v1 ctx ty spine) (@IROption.some (IRList IRTy) types)
      (ir_byte_field_types_set_writable_invariant_v1 ctx ty spine index replacement writable) typesFound
  @Eq.trans Bool
    (ir_byte_value_matches_v1 ctx ty (IRScalar.aggv (ir_vals_set spine index replacement)))
    (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set spine index replacement)) types)
    Bool.true
    (ir_byte_field_aggregate_selected_spine_equation_v1 ctx ty (ir_vals_set spine index replacement) types updatedTypes)
    updatedTyped";

const SELECTED_INSERT_FROM_INPUTS: &str = r"def ir_byte_field_selected_insert_from_inputs_v1 (ctx : IRByteContextV1)
  (aggregateTy replacementTy selected : IRTy)
  (spine : IRScalar) (index : Nat) (types : IRList IRTy) (replacement : IRScalar)
  (inputAggregateValid : @Eq Bool
    (ir_byte_field_aggregate_valid_v1 ctx aggregateTy (IRScalar.aggv spine)) Bool.true)
  (writable : @Eq Bool (ir_byte_field_writable_v1 aggregateTy index) Bool.true)
  (typesFound : @Eq (IROption (IRList IRTy))
    (ir_byte_field_types_v1 ctx aggregateTy spine) (@IROption.some (IRList IRTy) types))
  (laneFound : @Eq (IROption IRTy)
    (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
  (nominal : @Eq Bool (ir_byte_ty_eq_v1 selected replacementTy) Bool.true)
  (replacementTyped : @Eq Bool (ir_byte_value_matches_v1 ctx selected replacement) Bool.true)
  (bounded : @Eq Bool (ir_nat_ltb index (ir_vals_len spine)) Bool.true) :
  @Eq IRStepResult
    (ir_byte_insert_typed_v1 ctx aggregateTy replacementTy (IRScalar.aggv spine) index replacement)
    (IRStepResult.value (IRScalar.aggv (ir_vals_set spine index replacement))) :=
  ir_byte_field_selected_insert_v1 ctx aggregateTy replacementTy selected spine index types replacement
    inputAggregateValid writable typesFound laneFound nominal replacementTyped bounded
    (ir_byte_field_inserted_value_admission_v1 ctx aggregateTy spine index types selected replacement
      inputAggregateValid writable typesFound laneFound replacementTyped)";

#[cfg(test)]
#[path = "eval_ir_byte_field_preservation_laws_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Input-only extraction law transferred from independently checked Lean.
//! Derives the selected output's admission; keeps runtime output guards and APIs.
//! Catalogs and nominal metadata are not authenticated Rust-source certificates.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_field_extract_laws_v1(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SELECTED_EXTRACT_FROM_INPUTS,
            "Selected extraction from computed input admission/lookups and reflected nominal equality, without assuming result admission.",
        )?;
        Ok(())
    }
}

const SELECTED_EXTRACT_FROM_INPUTS: &str = r"def ir_byte_field_selected_extract_from_inputs_v1 (ctx : IRByteContextV1)
  (aggregateTy fieldTy selected : IRTy) (spine : IRScalar) (index : Nat)
  (types : IRList IRTy) (value : IRScalar)
  (inputAggregateValid : @Eq Bool (ir_byte_field_aggregate_valid_v1 ctx aggregateTy (IRScalar.aggv spine)) Bool.true)
  (typesFound : @Eq (IROption (IRList IRTy))
    (ir_byte_field_types_v1 ctx aggregateTy spine) (@IROption.some (IRList IRTy) types))
  (laneFound : @Eq (IROption IRTy)
    (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
  (nominal : @Eq Bool (ir_byte_ty_eq_v1 selected fieldTy) Bool.true)
  (valueFound : @Eq (IROption IRScalar) (ir_vals_get spine index) (@IROption.some IRScalar value)) :
  @Eq IRStepResult (ir_byte_extract_typed_v1 ctx aggregateTy fieldTy (IRScalar.aggv spine) index)
    (IRStepResult.value value) :=
  let rootTyped : @Eq Bool (ir_byte_value_matches_v1 ctx aggregateTy (IRScalar.aggv spine)) Bool.true :=
    ir_byte_world_and_right_v1
      (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))
      (ir_byte_value_matches_v1 ctx aggregateTy (IRScalar.aggv spine))
      (ir_byte_world_and_right_v1
        (ir_byte_field_layouts_unique_v1 (ir_byte_context_layouts_v1 ctx))
        (Bool.and (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))
          (ir_byte_value_matches_v1 ctx aggregateTy (IRScalar.aggv spine))) inputAggregateValid)
  let spineTyped : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types) Bool.true :=
    @Eq.trans Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
      (ir_byte_value_matches_v1 ctx aggregateTy (IRScalar.aggv spine)) Bool.true
      (@Eq.symm Bool (ir_byte_value_matches_v1 ctx aggregateTy (IRScalar.aggv spine))
        (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types)
        (ir_byte_field_aggregate_selected_spine_equation_v1 ctx aggregateTy spine types typesFound))
      rootTyped
  let selectedTyped : @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true :=
    ir_byte_field_spine_get_typed_v1 ctx spine types index selected value
      spineTyped laneFound valueFound
  let resultTyped : @Eq Bool (ir_byte_value_matches_v1 ctx fieldTy value) Bool.true :=
    @Eq.subst IRTy (fun actual => @Eq Bool (ir_byte_value_matches_v1 ctx actual value) Bool.true)
      selected fieldTy (ir_byte_type_equality_sound_v1 selected fieldTy nominal) selectedTyped
  ir_byte_field_selected_extract_v1 ctx aggregateTy fieldTy selected spine index types value
    inputAggregateValid typesFound laneFound nominal valueFound resultTyped";

#[cfg(test)]
#[path = "eval_ir_byte_field_extract_laws_tests.rs"]
mod tests;

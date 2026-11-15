// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Universal, kernel-rechecked pointer-part transport from canonical input
//! bounds. The five nominal families remain distinct; no successful execution,
//! post-world, allocation, dereference, UTF-8 or vtable premise is assumed.

use crate::spec::{SpecError, Specification};

const SUPPORT: &[&str] = &[
    r"def ir_byte_pointer_value_succ_v1 (predecessor : Nat) :
  @Eq IRScalar (ir_byte_pointer_value_v1 (Nat.succ predecessor))
    (IRScalar.ptr_ (Nat.succ predecessor)) :=
ir_eq_cong Bool IRScalar
  (fun (zero : Bool) => @Bool.rec (fun (_ : Bool) => IRScalar)
    (IRScalar.ptr_ (Nat.succ predecessor)) IRScalar.nullptr_ zero)
  (ir_nat_eqb (Nat.succ predecessor) 0) Bool.false
  (ir_byte_eqb_succ_zero_v1 predecessor)",
    r"def ir_byte_pointer_canonical_v1 (ctx : IRByteContextV1) (address : Nat)
  (bounded : Nat.lt address ir_byte_limit_v1) :
  @Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ (ir_byte_pointer_value_v1 address)) Bool.true :=
@Nat.rec
  (fun (word : Nat) => Nat.lt word ir_byte_limit_v1 ->
    @Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ (ir_byte_pointer_value_v1 word)) Bool.true)
  (fun (_ : Nat.lt 0 ir_byte_limit_v1) => @Eq.refl Bool Bool.true)
  (fun (predecessor : Nat)
    (_ : Nat.lt predecessor ir_byte_limit_v1 ->
      @Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ (ir_byte_pointer_value_v1 predecessor)) Bool.true)
    (bound : Nat.lt (Nat.succ predecessor) ir_byte_limit_v1) =>
    @Eq.trans Bool
      (ir_byte_value_matches_v1 ctx IRTy.ptr_ (ir_byte_pointer_value_v1 (Nat.succ predecessor)))
      (ir_byte_value_matches_v1 ctx IRTy.ptr_ (IRScalar.ptr_ (Nat.succ predecessor))) Bool.true
      (ir_eq_cong IRScalar Bool (fun (value : IRScalar) => ir_byte_value_matches_v1 ctx IRTy.ptr_ value)
        (ir_byte_pointer_value_v1 (Nat.succ predecessor)) (IRScalar.ptr_ (Nat.succ predecessor))
        (ir_byte_pointer_value_succ_v1 predecessor))
      (ir_byte_pointer_value_fits_v1 ctx predecessor bound)) address bounded",
    r"def ir_byte_ptrparts_normalized_data_v1 (address : Nat) (metadata : IRScalar) :
  @Eq IRStepResult (ir_byte_ptrparts_value_v1 (ir_byte_pointer_value_v1 address) metadata)
    (ir_byte_ptrparts_at_v1 address metadata) :=
@Nat.rec
  (fun (word : Nat) => @Eq IRStepResult
    (ir_byte_ptrparts_value_v1 (ir_byte_pointer_value_v1 word) metadata)
    (ir_byte_ptrparts_at_v1 word metadata))
  (@Eq.refl IRStepResult (ir_byte_ptrparts_at_v1 0 metadata))
  (fun (predecessor : Nat)
    (_ : @Eq IRStepResult (ir_byte_ptrparts_value_v1 (ir_byte_pointer_value_v1 predecessor) metadata)
      (ir_byte_ptrparts_at_v1 predecessor metadata)) =>
    ir_eq_cong IRScalar IRStepResult (fun (value : IRScalar) => ir_byte_ptrparts_value_v1 value metadata)
      (ir_byte_pointer_value_v1 (Nat.succ predecessor)) (IRScalar.ptr_ (Nat.succ predecessor))
      (ir_byte_pointer_value_succ_v1 predecessor)) address",
    r"def ir_byte_ptrparts_normalized_vtable_v1 (address metadata : Nat) :
  @Eq IRStepResult (ir_byte_ptrparts_at_v1 address (ir_byte_pointer_value_v1 metadata))
    (IRStepResult.value (IRScalar.fat_ address metadata)) :=
@Nat.rec
  (fun (word : Nat) => @Eq IRStepResult (ir_byte_ptrparts_at_v1 address (ir_byte_pointer_value_v1 word))
    (IRStepResult.value (IRScalar.fat_ address word)))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.fat_ address 0)))
  (fun (predecessor : Nat)
    (_ : @Eq IRStepResult (ir_byte_ptrparts_at_v1 address (ir_byte_pointer_value_v1 predecessor))
      (IRStepResult.value (IRScalar.fat_ address predecessor))) =>
    ir_eq_cong IRScalar IRStepResult (fun (value : IRScalar) => ir_byte_ptrparts_at_v1 address value)
      (ir_byte_pointer_value_v1 (Nat.succ predecessor)) (IRScalar.ptr_ (Nat.succ predecessor))
      (ir_byte_pointer_value_succ_v1 predecessor)) metadata",
];

fn and_true(a: &str, b: &str, left: &str, right: &str) -> String {
    format!("ir_byte_function_and_true_v1 ({a}) ({b}) ({left}) ({right})")
}

fn bounded(word: &str, premise: &str) -> String {
    format!("ir_byte_ltb_of_lt_v1 {word} ir_byte_limit_v1 {premise}")
}

fn case_true(guard: &str, success: &str, expected: &str, premise: &str, step: &str) -> String {
    format!(
        "ir_byte_case_true_v1 IRStepResult ({guard})
  (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
  ({success}) ({expected}) ({premise}) ({step})"
    )
}

impl Specification {
    pub(super) fn add_eval_ir_byte_fat_laws_v1(&mut self) -> Result<(), SpecError> {
        for source in SUPPORT {
            self.add_recursive_def(source, "Canonical zero/nonzero pointer transport by Nat induction; no new execution or dereference assumption.")?;
        }
        // The recursive slice parameter and trait identity stay quantified.
        // Sharing the proof construction does not identify their IRTy values.
        for (name, parameters, kind, vtable) in [
            ("fatstr", "", "IRTy.fatstr_", false),
            (
                "fatslice",
                "(element : IRTy)",
                "IRTy.fatslice_ element",
                false,
            ),
            ("fatdyn", "(traitId : Nat)", "IRTy.fatdyn_ traitId", true),
            ("containerlen", "", "IRTy.containerlen_", false),
            ("containervtable", "", "IRTy.containervtable_", true),
        ] {
            let mt = if vtable { "IRTy.ptr_" } else { "IRTy.uint_ 64" };
            let mv = if vtable {
                "ir_byte_pointer_value_v1 metadata"
            } else {
                "IRScalar.int_ metadata"
            };
            let telescope = format!(
                "(ctx : IRByteContextV1) {parameters} (data metadata : Nat)
  (dataBound : Nat.lt data ir_byte_limit_v1)
  (metadataBound : Nat.lt metadata ir_byte_limit_v1)"
            );
            let data_guard = "ir_nat_ltb data ir_byte_limit_v1";
            let metadata_guard = "ir_nat_ltb metadata ir_byte_limit_v1";
            let guard = format!("Bool.and ({data_guard}) ({metadata_guard})");
            let guard_proof = and_true(
                data_guard,
                metadata_guard,
                &bounded("data", "dataBound"),
                &bounded("metadata", "metadataBound"),
            );
            for (operation, lhs, value) in [
                (
                    "data",
                    format!("ir_byte_ptrdata_eval_v1 ctx ({kind}) (IRScalar.fat_ data metadata)"),
                    "ir_byte_pointer_value_v1 data".to_string(),
                ),
                (
                    "metadata",
                    format!("ir_byte_ptrmetadata_eval_v1 ctx ({kind}) ({mt}) (IRScalar.fat_ data metadata)"),
                    mv.to_string(),
                ),
            ] {
                let expected = format!("IRStepResult.value ({value})");
                let proof = case_true(
                    &guard,
                    &expected,
                    &expected,
                    &guard_proof,
                    &format!("@Eq.refl IRStepResult ({expected})"),
                );
                self.add_recursive_def(
                    &format!("def ir_byte_{name}_{operation}_v1 {telescope} :\n  @Eq IRStepResult ({lhs}) ({expected}) :=\n{proof}"),
                    "General typed fat-pointer projection derived from both canonical input word bounds. The kind and metadata sort are retained; no semantic output is a premise.",
                )?;
            }
            let data_fit = "ir_byte_value_matches_v1 ctx IRTy.ptr_ (ir_byte_pointer_value_v1 data)";
            let metadata_fit = format!("ir_byte_value_matches_v1 ctx ({mt}) ({mv})");
            let metadata_fit_proof = if vtable {
                "ir_byte_pointer_canonical_v1 ctx metadata metadataBound".to_string()
            } else {
                format!(
                    "ir_byte_u64_value_fits_v1 ctx metadata ({})",
                    bounded("metadata", "metadataBound")
                )
            };
            let parts_guard = format!("Bool.and ({data_fit}) ({metadata_fit})");
            let parts_guard_proof = and_true(
                data_fit,
                &metadata_fit,
                "ir_byte_pointer_canonical_v1 ctx data dataBound",
                &metadata_fit_proof,
            );
            let compute =
                format!("ir_byte_ptrparts_value_v1 (ir_byte_pointer_value_v1 data) ({mv})");
            let expected = "IRStepResult.value (IRScalar.fat_ data metadata)";
            let compute_proof = if vtable {
                format!("@Eq.trans IRStepResult ({compute}) (ir_byte_ptrparts_at_v1 data ({mv})) ({expected})
  (ir_byte_ptrparts_normalized_data_v1 data ({mv}))
  (ir_byte_ptrparts_normalized_vtable_v1 data metadata)")
            } else {
                format!("ir_byte_ptrparts_normalized_data_v1 data ({mv})")
            };
            let proof = case_true(
                &parts_guard,
                &compute,
                expected,
                &parts_guard_proof,
                &compute_proof,
            );
            self.add_recursive_def(
                &format!("def ir_byte_{name}_fromparts_v1 {telescope} :
  @Eq IRStepResult (ir_byte_ptrfromparts_eval_v1 ctx ({kind}) ({mt})
    (ir_byte_pointer_value_v1 data) ({mv})) ({expected}) :=\n{proof}"),
                "General typed fat-pointer assembly from canonical input words, including zero. Pointer metadata remains a pointer, length metadata remains U64; no allocation or validity right is inferred.",
            )?;
        }
        Ok(())
    }
}

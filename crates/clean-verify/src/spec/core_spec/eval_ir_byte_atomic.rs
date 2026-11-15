// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sequential prerequisite for a relaxed u64 fetch-add, using the actual
//! checked byte load/store and wrapping integer evaluator. This is not a
//! concurrent memory model: there are no interleavings or synchronization
//! claims. The separate fetched-step laws compose this primitive through the
//! sequential instruction dispatcher; neither these definitions nor that
//! composition authenticate source reflection or certify an Arc implementation.

use crate::spec::{SpecError, Specification};

pub(super) fn with_declaration_name(name: &str, error: SpecError) -> SpecError {
    match error {
        SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
        SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
        SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
        SpecError::EnvError(detail) => SpecError::EnvError(format!("{name}: {detail}")),
        // A budget failure is not a failed mathematical proof. Preserve its
        // structured declaration/resource diagnostics, as the byte loader does.
        other => other,
    }
}

const DEFINITIONS: &[(&str, &str)] = &[
    (
        "ir_byte_fetch_add_return_old_v1",
        r"def ir_byte_fetch_add_return_old_v1 (old : IRScalar)
  (result : IRByteMemoryResultV1) : IRByteMemoryResultV1 :=
match result with
| IRByteMemoryResultV1.value ignored memory => IRByteMemoryResultV1.value old memory
| IRByteMemoryResultV1.fault outcome memory => IRByteMemoryResultV1.fault outcome memory",
    ),
    (
        "ir_byte_fetch_add_after_arithmetic_v1",
        r"def ir_byte_fetch_add_after_arithmetic_v1 (ctx : IRByteContextV1)
  (ptr old : IRScalar) (mem : IRByteMemoryV1) (result : IRStepResult) : IRByteMemoryResultV1 :=
match result with
| IRStepResult.value updated => ir_byte_fetch_add_return_old_v1 old
    (ir_byte_store_v1 ctx (IRTy.uint_ 64) ptr updated 8 Bool.false mem)
| IRStepResult.fault outcome => IRByteMemoryResultV1.fault outcome mem",
    ),
    (
        "ir_byte_fetch_add_after_load_v1",
        r"def ir_byte_fetch_add_after_load_v1 (ctx : IRByteContextV1)
  (ptr delta : IRScalar) (result : IRByteMemoryResultV1) : IRByteMemoryResultV1 :=
match result with
| IRByteMemoryResultV1.value old memory =>
    @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
      (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) memory)
      (ir_byte_fetch_add_after_arithmetic_v1 ctx ptr old memory
        (ir_binop_eval IRBinOp.add (IRTy.uint_ 64) old delta))
      (ir_byte_value_matches_v1 ctx (IRTy.uint_ 64) delta)
| IRByteMemoryResultV1.fault outcome memory => IRByteMemoryResultV1.fault outcome memory",
    ),
    (
        "ir_byte_fetch_add_relaxed_u64_seq_v1",
        r"def ir_byte_fetch_add_relaxed_u64_seq_v1 (ctx : IRByteContextV1)
  (ptr delta : IRScalar) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
ir_byte_fetch_add_after_load_v1 ctx ptr delta
  (ir_byte_load_v1 ctx (IRTy.uint_ 64) ptr 8 Bool.false mem)",
    ),
    (
        "ir_byte_u64_rep_v1",
        r"def ir_byte_u64_rep_v1 (mem : IRByteMemoryV1) (p n : Nat) : Prop :=
forall (i : Nat), Nat.lt i 8 ->
  @Eq (IROption Nat) (ir_byte_mem_bytes_v1 mem (Nat.add p i))
    (@IROption.some Nat (Nat.mod (Nat.div n (ir_nat_pow2 (Nat.mul 8 i))) 256))",
    ),
    (
        "ir_byte_fetch_add_memory_v1",
        r"def ir_byte_fetch_add_memory_v1 (result : IRByteMemoryResultV1) : IRByteMemoryV1 :=
match result with
| IRByteMemoryResultV1.value old memory => memory
| IRByteMemoryResultV1.fault outcome memory => memory",
    ),
    (
        "ir_byte_fetch_add_old_v1",
        r"def ir_byte_fetch_add_old_v1 (result : IRByteMemoryResultV1) : IROption IRScalar :=
match result with
| IRByteMemoryResultV1.value old memory => @IROption.some IRScalar old
| IRByteMemoryResultV1.fault outcome memory => @IROption.none IRScalar",
    ),
];

impl Specification {
    pub(super) fn add_eval_ir_byte_atomic_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in DEFINITIONS {
            self.add_recursive_def(
                source,
                "Sequential u64 fetch-add prerequisite; no concurrent, reflected-instruction, or native authority.",
            )
            .map_err(|error| with_declaration_name(name, error))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

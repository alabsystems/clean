// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Distinct target-indexed Usize in the LE64 byte profile. Neither the type
//! nor its memory accesses are aliases of U64. Shared untyped byte/bit-pattern
//! facts are reusable; target authentication still belongs to reflection.
//! This sequential operation establishes no concurrent atomicity or Arc law.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const DEFINITIONS: &[(&str, &str)] = &[
    (
        "ir_byte_const_eval_v1",
        r"def ir_byte_const_eval_v1 (ty : IRTy) (value : IRConst) : IRStepResult :=
match ty with
| IRTy.usize_ bits =>
  @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded))
    (match value with
    | IRConst.int_ word => IRStepResult.value (IRScalar.int_ (ir_wrap bits word))
    | _ => IRStepResult.fault (IROutcome.type_error IRFault.not_int))
    (ir_nat_eqb bits 64)
| _ => ir_const_eval ty value",
    ),
    (
        "ir_byte_usize_add_v1",
        r"def ir_byte_usize_add_v1 (bits : Nat) (a b : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult)
  (IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded))
  (ir_int2 (fun (x y : Nat) => IRStepResult.value (IRScalar.int_ (ir_wrap bits (Nat.add x y)))) a b)
  (ir_nat_eqb bits 64)",
    ),
    (
        "ir_byte_fetch_add_usize64_after_arithmetic_v1",
        r"def ir_byte_fetch_add_usize64_after_arithmetic_v1 (ctx : IRByteContextV1)
  (ptr old : IRScalar) (mem : IRByteMemoryV1) (result : IRStepResult) : IRByteMemoryResultV1 :=
match result with
| IRStepResult.value updated => ir_byte_fetch_add_return_old_v1 old
    (ir_byte_store_v1 ctx (IRTy.usize_ 64) ptr updated 8 Bool.false mem)
| IRStepResult.fault outcome => IRByteMemoryResultV1.fault outcome mem",
    ),
    (
        "ir_byte_fetch_add_usize64_after_load_v1",
        r"def ir_byte_fetch_add_usize64_after_load_v1 (ctx : IRByteContextV1)
  (ptr delta : IRScalar) (result : IRByteMemoryResultV1) : IRByteMemoryResultV1 :=
match result with
| IRByteMemoryResultV1.value old memory =>
    @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
      (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) memory)
      (ir_byte_fetch_add_usize64_after_arithmetic_v1 ctx ptr old memory
        (ir_byte_usize_add_v1 64 old delta))
      (ir_byte_value_matches_v1 ctx (IRTy.usize_ 64) delta)
| IRByteMemoryResultV1.fault outcome memory => IRByteMemoryResultV1.fault outcome memory",
    ),
    (
        "ir_byte_fetch_add_relaxed_usize_seq_v1",
        r"def ir_byte_fetch_add_relaxed_usize_seq_v1 (bits : Nat) (ctx : IRByteContextV1)
  (ptr delta : IRScalar) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
  (ir_byte_fetch_add_usize64_after_load_v1 ctx ptr delta
    (ir_byte_load_v1 ctx (IRTy.usize_ bits) ptr 8 Bool.false mem))
  (ir_nat_eqb bits 64)",
    ),
    (
        "ir_byte_usize64_rep_v1",
        r"def ir_byte_usize64_rep_v1 (mem : IRByteMemoryV1) (p n : Nat) : Prop :=
forall (i : Nat), Nat.lt i 8 ->
  @Eq (IROption Nat) (ir_byte_mem_bytes_v1 mem (Nat.add p i))
    (@IROption.some Nat (Nat.mod (Nat.div n (ir_nat_pow2 (Nat.mul 8 i))) 256))",
    ),
    (
        "ir_byte_usize64_value_fits_v1",
        r"def ir_byte_usize64_value_fits_v1 (ctx : IRByteContextV1) (word : Nat)
  (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.usize_ 64) (IRScalar.int_ word)) Bool.true := h",
    ),
    (
        "ir_byte_usize64_lane_eight_v1",
        r"def ir_byte_usize64_lane_eight_v1 :
@Eq (IROption Nat) (ir_byte_lane_size_v1 (IRTy.usize_ 64)) (@IROption.some Nat 8) :=
@Eq.refl (IROption Nat) (@IROption.some Nat 8)",
    ),
    (
        "ir_byte_add_usize64_below_v1",
        r"def ir_byte_add_usize64_below_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 64)) Bool.true) :
  @Eq IRStepResult (ir_byte_usize_add_v1 64 (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_ (Nat.add a b))) :=
ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word))
  (ir_wrap 64 (Nat.add a b)) (Nat.add a b) (ir_byte_wrap_canonical_v1 64 (Nat.add a b) h)",
    ),
];

/// Instantiate proof-source templates, not an equality or cast between types.
/// The U64 declarations remain unchanged. Each new statement AND its proof are
/// elaborated and kernel-checked against the distinct Usize operational body.
/// Shared byte-range/codec lemmas contain no integer nominal identity.
fn usize_source(source: &str) -> String {
    let mut source = source.to_owned();
    for (from, to) in [
        (
            "IRInst.atomic_fetch_add_relaxed_u64_seq",
            "IRInst.atomic_fetch_add_relaxed_usize_seq 64",
        ),
        (
            "ir_byte_fetch_add_relaxed_u64_seq_v1",
            "ir_byte_fetch_add_relaxed_usize_seq_v1 64",
        ),
        ("relaxed_u64_seq", "relaxed_usize64_seq"),
        ("IRTy.uint_ 64", "IRTy.usize_ 64"),
        ("ir_byte_u64_", "ir_byte_usize64_"),
        (
            "ir_byte_fetch_add_after_arithmetic_v1",
            "ir_byte_fetch_add_usize64_after_arithmetic_v1",
        ),
        (
            "ir_byte_fetch_add_after_load_v1",
            "ir_byte_fetch_add_usize64_after_load_v1",
        ),
        (
            "ir_binop_eval IRBinOp.add (IRTy.usize_ 64)",
            "ir_byte_usize_add_v1 64",
        ),
        (
            "ir_byte_add_uint_below_v1 64",
            "ir_byte_add_usize64_below_v1",
        ),
    ] {
        source = source.replace(from, to);
    }
    source
}

impl Specification {
    pub(super) fn add_eval_ir_byte_usize_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in DEFINITIONS {
            self.add_recursive_def(source,
                "Distinct LE64 Usize byte operation; legacy arithmetic, other target widths and concurrent/source authority are not admitted.")
                .map_err(|error| with_declaration_name(name, error))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_usize_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in super::eval_ir_byte_atomic_laws::laws()
            .into_iter()
            .chain(super::eval_ir_byte_atomic_step_laws::laws())
        {
            let name = usize_source(name);
            let source = usize_source(&source);
            self.add_recursive_def(&source,
                "Representation-derived sequential Usize64 execution and whole fetched world. No successful-execution/post-world premise or concurrent/source authority.")
                .map_err(|error| with_declaration_name(&name, error))?;
            self.verify_definition(&name)?;
        }
        Ok(())
    }
}

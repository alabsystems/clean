// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ByteV1 comparisons for pointer addresses, Bool and nominal Usize64.
//! Address exposure does not dereference a pointer or establish allocation
//! ownership. The legacy cell profile retains its separate semantics.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const POINTER_ADDRESS: &str = r"def ir_byte_pointer_comparison_address_at_v1
  (bits : Nat) (value : IRScalar) : IRStepResult :=
match value with
| IRScalar.ptr_ address => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.ub IRFault.bad_addr))
    (IRStepResult.value (IRScalar.int_ address))
    (ir_nat_ltb address (ir_nat_pow2 bits))
| IRScalar.nullptr_ => IRStepResult.value (IRScalar.int_ 0)
| _ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)";

const POINTER_COMPARE: &str = r"def ir_byte_pointer_icmp_at_v1
  (op : IRICmpOp) (bits : Nat) (a b : IRScalar) : IRStepResult :=
match a with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.ub IRFault.uninit)
| _ => match b with
  | IRScalar.undef_ => IRStepResult.fault (IROutcome.ub IRFault.uninit)
  | _ => @Bool.rec (fun (_ : Bool) => IRStepResult)
      (IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded))
      (match ir_byte_pointer_comparison_address_at_v1 bits a with
       | IRStepResult.fault outcome => IRStepResult.fault outcome
       | IRStepResult.value left =>
         match ir_byte_pointer_comparison_address_at_v1 bits b with
         | IRStepResult.fault outcome => IRStepResult.fault outcome
         | IRStepResult.value right => ir_icmp_eval op (IRTy.uint_ bits) left right)
      (Bool.or (ir_nat_eqb bits 32) (ir_nat_eqb bits 64))";

const BOOL_COMPARE: &str = r"def ir_byte_bool_icmp_v1
  (op : IRICmpOp) (a b : IRScalar) : IRStepResult :=
match a with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.ub IRFault.uninit)
| _ => match b with
  | IRScalar.undef_ => IRStepResult.fault (IROutcome.ub IRFault.uninit)
  | _ => match a with
    | IRScalar.bool_ left => match b with
      | IRScalar.bool_ right => ir_icmp_eval op (IRTy.uint_ 1)
          (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) 0 1 left))
          (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) 0 1 right))
      | _ => IRStepResult.fault (IROutcome.type_error IRFault.not_bool)
    | _ => IRStepResult.fault (IROutcome.type_error IRFault.not_bool)";

const EVALUATOR: &str = r"def ir_byte_icmp_eval_v1 (op : IRICmpOp) (ty : IRTy)
  (a b : IRScalar) : IRStepResult :=
match ty with
| IRTy.ptr_ => ir_byte_pointer_icmp_at_v1 op 64 a b
| IRTy.bool_ => ir_byte_bool_icmp_v1 op a b
| IRTy.usize_ bits =>
  @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded))
    (ir_icmp_eval op (IRTy.uint_ bits) a b)
    (ir_nat_eqb bits 64)
| _ => ir_icmp_eval op ty a b";

const CANONICAL: &str = r"def ir_byte_icmp_usize64_ugt_canonical_v1 (a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 64)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 64)) Bool.true) :
@Eq IRStepResult
  (ir_byte_icmp_eval_v1 IRICmpOp.ugt (IRTy.usize_ 64) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_ltb b a))) :=
@Eq.trans IRStepResult
  (ir_byte_icmp_eval_v1 IRICmpOp.ugt (IRTy.usize_ 64) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_ltb (ir_wrap 64 b) a)))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_ltb b a)))
  (ir_eq_cong Nat IRStepResult
    (fun (x : Nat) => IRStepResult.value (IRScalar.bool_ (ir_nat_ltb (ir_wrap 64 b) x)))
    (ir_wrap 64 a) a (ir_byte_wrap_canonical_v1 64 a aFits))
  (ir_eq_cong Nat IRStepResult
    (fun (y : Nat) => IRStepResult.value (IRScalar.bool_ (ir_nat_ltb y a)))
    (ir_wrap 64 b) b (ir_byte_wrap_canonical_v1 64 b bFits))";

fn ordered(name: &str, premise: &str, value: &str, proof: &str) -> String {
    format!(
        "def {name} (a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 64)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 64)) Bool.true)
  (ordered : {premise}) :
@Eq IRStepResult
  (ir_byte_icmp_eval_v1 IRICmpOp.ugt (IRTy.usize_ 64) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ {value})) :=
@Eq.trans IRStepResult
  (ir_byte_icmp_eval_v1 IRICmpOp.ugt (IRTy.usize_ 64) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_ltb b a)))
  (IRStepResult.value (IRScalar.bool_ {value}))
  (ir_byte_icmp_usize64_ugt_canonical_v1 a b aFits bFits)
  (ir_eq_cong Bool IRStepResult (fun (flag : Bool) => IRStepResult.value (IRScalar.bool_ flag))
    (ir_nat_ltb b a) {value} ({proof}))"
    )
}

impl Specification {
    pub(super) fn add_eval_ir_byte_usize_cmp_v1(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            POINTER_ADDRESS,
            "Width-checked data-pointer address exposure for comparisons; no dereference, live-allocation or ownership premise is inferred.",
        )?;
        self.add_recursive_def(
            POINTER_COMPARE,
            "All ten pointer comparison predicates over exact 32/64-bit address patterns; poison and out-of-target addresses refuse before comparison. The complete ByteV1 machine remains 64-bit.",
        )?;
        self.add_recursive_def(
            BOOL_COMPARE,
            "Bool comparisons use exact one-bit patterns: true is unsigned 1 and signed -1. Either poison operand refuses before conversion; malformed carriers are not booleans.",
        )?;
        self.add_recursive_def(EVALUATOR,
            "Byte-only pointer-address, one-bit Bool and nominal Usize64 comparisons. Other widths and nominal cases retain their existing boundaries; no source or native authority.")?;
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_usize_cmp_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in [
            (
                "ir_byte_icmp_usize64_ugt_canonical_v1",
                CANONICAL.to_owned(),
            ),
            (
                "ir_byte_icmp_usize64_ugt_le_v1",
                ordered(
                    "ir_byte_icmp_usize64_ugt_le_v1",
                    "Nat.le a b",
                    "Bool.false",
                    "ir_byte_allocation_ltb_false_v1 b a ordered",
                ),
            ),
            (
                "ir_byte_icmp_usize64_ugt_lt_v1",
                ordered(
                    "ir_byte_icmp_usize64_ugt_lt_v1",
                    "Nat.lt b a",
                    "Bool.true",
                    "ir_byte_ltb_of_lt_v1 b a ordered",
                ),
            ),
        ] {
            self.add_recursive_def(&source,
                "Checked strict Usize64 comparison from input bit-pattern bounds/order, not an assumed comparison answer.")
                .map_err(|error| with_declaration_name(name, error))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

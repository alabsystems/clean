// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked casts for the byte/world profile, not the legacy cell machine.
//!
//! Canonical integer conversions reuse the existing scalar evaluator. Thin
//! pointer conversions use this profile's zero/null and 64-bit address rules.
//! Constructing a pointer VALUE does not allocate, establish provenance, prove
//! liveness/alignment, or permit a dereference or an indirect function call.
//! Bitcast additionally preserves an already canonical opaque Ptr carrier;
//! typed references, mixed pointer/integer and fat-pointer Bitcasts stay out.

use crate::spec::{SpecError, Specification};

impl Specification {
    /// Install after byte types/memory and before the actual machine dispatch.
    /// The public byte constructor independently checks/audits these roots.
    pub(super) fn add_eval_ir_byte_cast_v1(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (
                r"def ir_byte_cast_integer_ty_v1 (ty : IRTy) : Bool :=
@IROption.rec Nat (fun (_ : IROption Nat) => Bool) Bool.false
  (fun (width : Nat) => Bool.and (ir_nat_pos width) (ir_nat_leb width 128))
  (ir_ty_int_width ty)",
                "The byte scalar integer frontier: signed/unsigned canonical bit patterns at widths 1 through 128; Bool is a distinct carrier.",
            ),
            (
                r"def ir_byte_cast_width_v1 (ty : IRTy) : Nat := match ty with
| IRTy.bool_ => 1
| IRTy.int_ width => width
| IRTy.uint_ width => width
| _ => 0",
                "Width projection used only together with explicit type-family admission; zero is not an admitted width.",
            ),
            (
                r"def ir_byte_cast_numeric_ty_v1 (ty : IRTy) : Bool :=
Bool.or (ir_byte_cast_integer_ty_v1 ty) (ir_byte_ty_eq_v1 ty IRTy.bool_)",
                "The distinct Bool and canonical integer families used by truncation and extension.",
            ),
            (
                r"def ir_byte_cast_word_ty_v1 (ty : IRTy) : Bool :=
Bool.and (ir_byte_cast_integer_ty_v1 ty) (ir_nat_eqb (ir_byte_cast_width_v1 ty) 64)",
                "Pointer/integer conversions in this 64-bit byte profile use exactly I64/U64; other widths are explicitly unsupported.",
            ),
            (
                r"def ir_byte_cast_supported_v1 (op : IRCastOp) (src : IRTy) (dst : IRTy) : Bool :=
match op with
| IRCastOp.trunc => Bool.and (ir_byte_cast_integer_ty_v1 src)
    (Bool.and (ir_byte_cast_numeric_ty_v1 dst) (ir_nat_leb (ir_byte_cast_width_v1 dst) (ir_byte_cast_width_v1 src)))
| IRCastOp.zext => Bool.and (ir_byte_cast_numeric_ty_v1 src)
    (Bool.and (ir_byte_cast_integer_ty_v1 dst) (ir_nat_leb (ir_byte_cast_width_v1 src) (ir_byte_cast_width_v1 dst)))
| IRCastOp.sext => Bool.and (ir_byte_cast_numeric_ty_v1 src)
    (Bool.and (ir_byte_cast_integer_ty_v1 dst) (ir_nat_leb (ir_byte_cast_width_v1 src) (ir_byte_cast_width_v1 dst)))
| IRCastOp.bitcast => Bool.or
    (Bool.and (ir_byte_ty_eq_v1 src IRTy.ptr_) (ir_byte_ty_eq_v1 dst IRTy.ptr_))
    (Bool.and (ir_byte_cast_integer_ty_v1 src)
      (Bool.and (ir_byte_cast_integer_ty_v1 dst) (ir_nat_eqb (ir_byte_cast_width_v1 src) (ir_byte_cast_width_v1 dst))))
| IRCastOp.inttoptr => Bool.and (ir_byte_cast_word_ty_v1 src) (ir_byte_pointer_ty_v1 dst)
| IRCastOp.ptrtoint => Bool.and (ir_byte_pointer_ty_v1 src) (ir_byte_cast_word_ty_v1 dst)
| IRCastOp.ptrtoptr => Bool.and (ir_byte_pointer_ty_v1 src) (ir_byte_pointer_ty_v1 dst)
| _ => Bool.false",
                "Exact opcode/type/width frontier; float, transmute, function and fat-pointer conversions do not borrow unrelated legacy meanings.",
            ),
            (
                r"def ir_byte_cast_result_v1 (ctx : IRByteContextV1) (dst : IRTy) (r : IRStepResult) : IRStepResult :=
match r with
| IRStepResult.value value => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (IRStepResult.value value) (ir_byte_value_matches_v1 ctx dst value)
| IRStepResult.fault fault => IRStepResult.fault fault",
                "A successful cast must inhabit its own declared destination, independently of the fetched site's separate result-lane check; faults are preserved exactly.",
            ),
            (
                r"def ir_byte_cast_compute_v1 (op : IRCastOp) (src : IRTy) (dst : IRTy) (value : IRScalar) : IRStepResult :=
match op with
| IRCastOp.inttoptr => match value with
  | IRScalar.int_ word => IRStepResult.value (ir_byte_pointer_value_v1 word)
  | _ => IRStepResult.fault (IROutcome.type_error IRFault.bad_field)
| IRCastOp.ptrtoint => @IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word))
    (ir_byte_pointer_address_v1 value)
| IRCastOp.ptrtoptr => IRStepResult.value value
| IRCastOp.bitcast => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (ir_cast_eval IRCastOp.bitcast src dst value) (IRStepResult.value value)
    (Bool.and (ir_byte_ty_eq_v1 src IRTy.ptr_) (ir_byte_ty_eq_v1 dst IRTy.ptr_))
| _ => ir_cast_eval op src dst value",
                "Private computation behind explicit admission: canonical integer casts retain the existing evaluator; byte pointers reserve zero for nullptr and never mint allocations.",
            ),
            (
                r"def ir_byte_cast_eval_v1 (ctx : IRByteContextV1) (op : IRCastOp) (src : IRTy) (dst : IRTy) (value : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault
  (@Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (ir_byte_cast_result_v1 ctx dst (ir_byte_cast_compute_v1 op src dst value))
    (ir_byte_value_matches_v1 ctx src value))
  (ir_byte_cast_supported_v1 op src dst)",
                "Byte-specific typed cast: unsupported opcode/types/widths refuse first; malformed or noncanonical admitted carriers fail bad_field. Both success and failure are pure with respect to the byte/provider world.",
            ),
            (
                r"def ir_byte_bitcast_ptr_identity_v1 (ctx : IRByteContextV1) (value : IRScalar)
  (canonical : @Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ value) Bool.true) :
  @Eq IRStepResult (ir_byte_cast_eval_v1 ctx IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ value)
    (IRStepResult.value value) :=
@Eq.subst Bool
  (fun (ok : Bool) => @Eq IRStepResult
    (@Bool.rec (fun (_ : Bool) => IRStepResult)
      (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
      (@Bool.rec (fun (_ : Bool) => IRStepResult)
        (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
        (IRStepResult.value value) ok) ok)
    (IRStepResult.value value))
  Bool.true (ir_byte_value_matches_v1 ctx IRTy.ptr_ value)
  (@Eq.symm Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ value) Bool.true canonical)
  (@Eq.refl IRStepResult (IRStepResult.value value))",
                "Canonical opaque Ptr-to-Ptr Bitcast is the identity; carrier representation is a premise, successful evaluation and memory access are not.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_cast_tests.rs"]
mod tests;

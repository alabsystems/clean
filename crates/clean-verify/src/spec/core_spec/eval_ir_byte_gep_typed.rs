// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in nominal GEP indices over the original SSA IDs and machine.
//!
//! The old mk/mkt sites keep their exact erased signed-64 denotation. Only
//! mki reads the nominal operand catalog: negative narrow signed words cannot
//! become positive addresses, and unsigned narrow words retain their full
//! canonical range. I64/U64 keep the existing bound below 2^63. Other widths,
//! missing or ambiguous metadata, and noncanonical carriers remain refused.
//! This is a checked operational definition, not source or native authority.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_gep_typed_v1(&mut self) -> Result<(), SpecError> {
        // Install after field catalogs, before actual Byte instruction dispatch.
        // No unchecked declarations, alternate evaluator or extra proof budget.
        for source in [
            r"def ir_byte_gep_index_limit_v1 (ty : IRTy) : IROption Nat := match ty with
| IRTy.int_ width =>
  @Bool.rec (fun (_ : Bool) => IROption Nat)
    (@Bool.rec (fun (_ : Bool) => IROption Nat)
      (@Bool.rec (fun (_ : Bool) => IROption Nat)
        (@Bool.rec (fun (_ : Bool) => IROption Nat)
          (@IROption.none Nat) (@IROption.some Nat 9223372036854775808) (ir_nat_eqb width 64))
        (@IROption.some Nat 2147483648) (ir_nat_eqb width 32))
      (@IROption.some Nat 32768) (ir_nat_eqb width 16))
    (@IROption.some Nat 128) (ir_nat_eqb width 8)
| IRTy.uint_ width =>
  @Bool.rec (fun (_ : Bool) => IROption Nat)
    (@Bool.rec (fun (_ : Bool) => IROption Nat)
      (@Bool.rec (fun (_ : Bool) => IROption Nat)
        (@Bool.rec (fun (_ : Bool) => IROption Nat)
          (@IROption.none Nat) (@IROption.some Nat 9223372036854775808) (ir_nat_eqb width 64))
        (@IROption.some Nat 4294967296) (ir_nat_eqb width 32))
      (@IROption.some Nat 65536) (ir_nat_eqb width 16))
    (@IROption.some Nat 256) (ir_nat_eqb width 8)
| _ => @IROption.none Nat",
            r"def ir_byte_gep_typed_index_v1 (ty : IRTy) (value : IRScalar) : IROption Nat := match value with
| IRScalar.int_ n =>
  @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) (@IROption.none Nat)
    (fun (limit : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
      (@IROption.none Nat) (@IROption.some Nat n) (ir_nat_ltb n limit))
    (ir_byte_gep_index_limit_v1 ty)
| _ => @IROption.none Nat",
            r"def ir_byte_gep_typed_indices_v1 (rows : IRList IRByteOperandV1)
  (s : IRMachine) (ids : IRList Nat) : IROption Nat :=
@Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat)
  (@IRList.rec Nat (fun (_ : IRList Nat) => IROption Nat) (@IROption.some Nat 0)
    (fun (id : Nat) (_ : IRList Nat) (ih : IROption Nat) =>
      @IROption.rec IRTy (fun (_ : IROption IRTy) => IROption Nat) (@IROption.none Nat)
        (fun (ty : IRTy) =>
          @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) (@IROption.none Nat)
            (fun (index : Nat) =>
              @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) (@IROption.none Nat)
                (fun (rest : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
                  (@IROption.none Nat) (@IROption.some Nat (Nat.add index rest))
                  (ir_nat_ltb (Nat.add index rest) ir_byte_limit_v1)) ih)
            (ir_byte_gep_typed_index_v1 ty (ir_getd s id)))
        (ir_byte_operand_find_v1 rows id)) ids)
  (ir_byte_operands_unique_v1 rows)",
            r"def ir_byte_gep_typed_v1 (ctx : IRByteContextV1) (pointeeTy : IRTy)
  (base : IRScalar) (indices : IROption Nat) (inbounds : Bool) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
  (fun (layout : IRByteLayoutV1) => @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
    (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
    (@IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
      (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
      (fun (index : Nat) =>
        @IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
          (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.not_ptr) mem)
          (fun (address : Nat) => ir_byte_gep_at_v1 address (ir_byte_layout_size_v1 layout) index inbounds mem)
          (ir_byte_pointer_address_v1 base)) indices)
    (Bool.and (ir_nat_pos (ir_byte_layout_size_v1 layout))
      (ir_nat_ltb (ir_byte_layout_size_v1 layout) ir_byte_limit_v1)))
  (ir_byte_layout_v1 ctx pointeeTy)",
            r"def ir_byte_gep_site_v1 (ctx : IRByteContextV1) (site : IRByteSiteV1)
  (pointeeTy : IRTy) (s : IRMachine) (base : Nat) (indices : IRList Nat)
  (inbounds : Bool) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 := match site with
| IRByteSiteV1.mki fid block pc align cc results rows =>
  ir_byte_gep_typed_v1 ctx pointeeTy (ir_getd s base)
    (ir_byte_gep_typed_indices_v1 rows s indices) inbounds mem
| _ => ir_byte_gep_v1 ctx pointeeTy (ir_getd s base) (ir_resolve s indices) inbounds mem",
            r"def ir_byte_gep_site_mk_legacy_v1 (ctx : IRByteContextV1)
  (fid block pc align cc : Nat) (results : IRList IRTy) (pointeeTy : IRTy)
  (s : IRMachine) (base : Nat) (indices : IRList Nat) (inbounds : Bool) (mem : IRByteMemoryV1) :
@Eq IRByteMemoryResultV1
  (ir_byte_gep_site_v1 ctx (IRByteSiteV1.mk fid block pc align cc results) pointeeTy s base indices inbounds mem)
  (ir_byte_gep_v1 ctx pointeeTy (ir_getd s base) (ir_resolve s indices) inbounds mem) :=
@Eq.refl IRByteMemoryResultV1 (ir_byte_gep_v1 ctx pointeeTy (ir_getd s base) (ir_resolve s indices) inbounds mem)",
            r"def ir_byte_gep_site_mkt_legacy_v1 (ctx : IRByteContextV1)
  (fid block pc align cc : Nat) (results : IRList IRTy) (rows : IRList IRByteOperandV1) (pointeeTy : IRTy)
  (s : IRMachine) (base : Nat) (indices : IRList Nat) (inbounds : Bool) (mem : IRByteMemoryV1) :
@Eq IRByteMemoryResultV1
  (ir_byte_gep_site_v1 ctx (IRByteSiteV1.mkt fid block pc align cc results rows) pointeeTy s base indices inbounds mem)
  (ir_byte_gep_v1 ctx pointeeTy (ir_getd s base) (ir_resolve s indices) inbounds mem) :=
@Eq.refl IRByteMemoryResultV1 (ir_byte_gep_v1 ctx pointeeTy (ir_getd s base) (ir_resolve s indices) inbounds mem)",
            r"def ir_byte_gep_site_mki_selected_v1 (ctx : IRByteContextV1)
  (fid block pc align cc : Nat) (results : IRList IRTy) (rows : IRList IRByteOperandV1) (pointeeTy : IRTy)
  (s : IRMachine) (base : Nat) (indices : IRList Nat) (inbounds : Bool) (mem : IRByteMemoryV1) (index : Nat)
  (resolved : @Eq (IROption Nat) (ir_byte_gep_typed_indices_v1 rows s indices) (@IROption.some Nat index)) :
@Eq IRByteMemoryResultV1
  (ir_byte_gep_site_v1 ctx (IRByteSiteV1.mki fid block pc align cc results rows) pointeeTy s base indices inbounds mem)
  (ir_byte_gep_typed_v1 ctx pointeeTy (ir_getd s base) (@IROption.some Nat index) inbounds mem) :=
ir_eq_cong (IROption Nat) IRByteMemoryResultV1
  (fun (decoded : IROption Nat) => ir_byte_gep_typed_v1 ctx pointeeTy (ir_getd s base) decoded inbounds mem)
  (ir_byte_gep_typed_indices_v1 rows s indices) (@IROption.some Nat index)
  resolved",
        ] {
            self.add_recursive_def(
                source,
                "Checked opt-in nominal GEP over original SSA IDs; old site denotation, layout/address checks and complete memory are retained. Not source/native authentication.",
            )?;
        }
        Ok(())
    }
}

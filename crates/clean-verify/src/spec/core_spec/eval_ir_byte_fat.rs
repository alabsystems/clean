// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed LE64 pointer parts. Kind identity belongs to IRTy, not to the two
//! numeric representation words. This grants no UTF-8, slice bounds, vtable
//! dispatch, allocation/provenance, native ABI or source-refinement authority.
//! The legacy fatptr_ constructor is deliberately not a ByteV1 type.

use crate::spec::{SpecError, Specification};

impl Specification {
    // Called before the value matcher; depends only on syntax/numeric helpers.
    pub(super) fn add_eval_ir_byte_fat_types_v1(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (r"def ir_byte_fat_metadata_ty_v1 (ty : IRTy) : IROption IRTy := match ty with
| IRTy.fatstr_ => @IROption.some IRTy (IRTy.uint_ 64)
| IRTy.fatslice_ element => @IROption.some IRTy (IRTy.uint_ 64)
| IRTy.fatdyn_ traitId => @IROption.some IRTy IRTy.ptr_
| IRTy.containerlen_ => @IROption.some IRTy (IRTy.uint_ 64)
| IRTy.containervtable_ => @IROption.some IRTy IRTy.ptr_
| _ => @IROption.none IRTy",
             "Canonical TrustIR LE64 metadata: U64 length versus opaque Ptr vtable. Identical physical lanes do not identify nominal fat kinds."),
            (r"def ir_byte_fat_value_matches_v1 (ty : IRTy) (data metadata : Nat) : Bool :=
@IROption.rec IRTy (fun (_ : IROption IRTy) => Bool) Bool.false
  (fun (_ : IRTy) => Bool.and (ir_nat_ltb data (ir_nat_pow2 64))
    (ir_nat_ltb metadata (ir_nat_pow2 64))) (ir_byte_fat_metadata_ty_v1 ty)",
             "Representation bounds for both words of the five explicit fat kinds; zero is allowed and confers no dereference right. This is not string or vtable validity."),
        ] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_fat_v1(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (r"def ir_byte_pointer_metadata_ty_v1 (ty : IRTy) : IROption IRTy :=
@Bool.rec (fun (_ : Bool) => IROption IRTy)
  (ir_byte_fat_metadata_ty_v1 ty) (@IROption.some IRTy IRTy.unit_)
  (ir_byte_pointer_ty_v1 ty)",
             "Canonical metadata of admitted thin pointers or the five explicit fat kinds. Legacy fatptr_, integer and function types are not pointer-part types."),
            (r"def ir_byte_ptrdata_value_v1 (value : IRScalar) : IRStepResult := match value with
| IRScalar.fat_ data metadata => IRStepResult.value (ir_byte_pointer_value_v1 data)
| IRScalar.ptr_ address => IRStepResult.value (IRScalar.ptr_ address)
| IRScalar.nullptr_ => IRStepResult.value IRScalar.nullptr_
| _ => IRStepResult.fault (IROutcome.type_error IRFault.bad_field)",
             "Data projection behind typed admission. The zero fat data word projects to canonical nullptr, never ptr_ 0."),
            (r"def ir_byte_ptrdata_eval_v1 (ctx : IRByteContextV1) (ptrTy : IRTy)
  (value : IRScalar) : IRStepResult :=
@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ir_width_fault
  (fun (_ : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (ir_byte_ptrdata_value_v1 value) (ir_byte_value_matches_v1 ctx ptrTy value))
  (ir_byte_pointer_metadata_ty_v1 ptrTy)",
             "Typed PtrData: exact declared pointer-family admission and canonical carrier checks before projection, without modifying memory or provider state."),
            (r"def ir_byte_ptrmetadata_value_v1 (metadataTy : IRTy) (value : IRScalar) : IRStepResult :=
match value with
| IRScalar.fat_ data metadata => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.value (IRScalar.int_ metadata))
    (IRStepResult.value (ir_byte_pointer_value_v1 metadata))
    (ir_byte_ty_eq_v1 metadataTy IRTy.ptr_)
| IRScalar.ptr_ address => IRStepResult.value IRScalar.unit_
| IRScalar.nullptr_ => IRStepResult.value IRScalar.unit_
| _ => IRStepResult.fault (IROutcome.type_error IRFault.bad_field)",
             "Private metadata projection after admission: integer length and canonical opaque vtable pointer remain different scalar sorts."),
            (r"def ir_byte_ptrmetadata_eval_v1 (ctx : IRByteContextV1) (ptrTy metadataTy : IRTy)
  (value : IRScalar) : IRStepResult :=
@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ir_width_fault
  (fun (canonical : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (ir_byte_ptrmetadata_value_v1 canonical value)
    (Bool.and (ir_byte_ty_eq_v1 metadataTy canonical)
      (ir_byte_value_matches_v1 ctx ptrTy value)))
  (ir_byte_pointer_metadata_ty_v1 ptrTy)",
             "Typed PtrMetadata checks its exact canonical metadata declaration independently of the fetched result-lane check; Usize is not relabeled U64."),
            (r"def ir_byte_ptrparts_at_v1 (address : Nat) (metadata : IRScalar) : IRStepResult :=
match metadata with
| IRScalar.int_ word => IRStepResult.value (IRScalar.fat_ address word)
| IRScalar.ptr_ word => IRStepResult.value (IRScalar.fat_ address word)
| IRScalar.nullptr_ => IRStepResult.value (IRScalar.fat_ address 0)
| IRScalar.unit_ => IRStepResult.value (ir_byte_pointer_value_v1 address)
| _ => IRStepResult.fault (IROutcome.type_error IRFault.bad_field)",
             "Private assembly behind exact sort checks. Function identities and poison never stand for vtable addresses."),
            (r"def ir_byte_ptrparts_value_v1 (data metadata : IRScalar) : IRStepResult := match data with
| IRScalar.ptr_ address => ir_byte_ptrparts_at_v1 address metadata
| IRScalar.nullptr_ => ir_byte_ptrparts_at_v1 0 metadata
| _ => IRStepResult.fault (IROutcome.type_error IRFault.bad_field)",
             "Only an explicit thin pointer supplies the data lane; fat pointers, integers and function IDs are not silently projected or reinterpreted."),
            (r"def ir_byte_ptrfromparts_eval_v1 (ctx : IRByteContextV1) (ptrTy metadataTy : IRTy)
  (data metadata : IRScalar) : IRStepResult :=
@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ir_width_fault
  (fun (canonical : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (ir_byte_ptrparts_value_v1 data metadata)
    (Bool.and (ir_byte_ty_eq_v1 metadataTy canonical)
      (Bool.and (ir_byte_value_matches_v1 ctx IRTy.ptr_ data)
        (ir_byte_value_matches_v1 ctx canonical metadata))))
  (ir_byte_pointer_metadata_ty_v1 ptrTy)",
             "Typed PtrFromParts retains exact metadata type, thin data and metadata sorts, null normalization and canonical word bounds. It never allocates or grants access."),
        ] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_fat_tests.rs"]
mod tests;

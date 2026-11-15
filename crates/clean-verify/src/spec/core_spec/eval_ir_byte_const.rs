// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Contextual conversion of complete SSA constants, not physical memory.
//!
//! The locked trust-ir interpreter converts aggregate constants against each
//! declared field type. In particular, a nested Int(0) at opaque Ptr and the
//! exact two-zero fat seed are not integer/aggregate runtime carriers. Fold
//! the finite constant tree, not the potentially cyclic schema graph. Catalog
//! authenticity, module validation, native layout and source refinement remain
//! separate obligations. Uninit, symbol addresses and partial aggregates are
//! not introduced. The legacy evaluator remains unchanged.
//! Integer wrapping is the existing model's bit-pattern convention, not raw
//! signed-literal validation parity. Enum selection uses the unwrapped
//! canonical tag word. Translating negative source discriminants and validating
//! unique function/catalog identities still belong to the source producer.

use crate::spec::{SpecError, Specification};

const BAD: &str = "IRStepResult.fault (IROutcome.type_error IRFault.bad_field)";
const ZERO_FAT: &str =
    "IRConst.aggv (IRConst.vcons (IRConst.int_ 0) (IRConst.vcons (IRConst.int_ 0) IRConst.vnil))";

impl Specification {
    pub(super) fn add_eval_ir_byte_const_v1(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive IRByteConstFoldV1 : Type\n| mk : (IRTy -> IRStepResult) -> (IRList IRTy -> IRStepResult) -> IRByteConstFoldV1",
            "Joint contextual constant/value and exact-field-spine conversion. No type-graph recursion or additional fuel bound.",
        )?;
        for source in [
            r"def ir_byte_const_value_at_v1 (fold : IRByteConstFoldV1) : IRTy -> IRStepResult := match fold with
| IRByteConstFoldV1.mk value fields => value",
            r"def ir_byte_const_fields_at_v1 (fold : IRByteConstFoldV1) : IRList IRTy -> IRStepResult := match fold with
| IRByteConstFoldV1.mk value fields => fields",
            r"def ir_byte_const_checked_v1 (ctx : IRByteContextV1) (ty : IRTy) (result : IRStepResult) : IRStepResult := match result with
| IRStepResult.value value => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) (IRStepResult.value value)
    (ir_byte_value_matches_v1 ctx ty value)
| IRStepResult.fault outcome => IRStepResult.fault outcome",
            r"def ir_byte_const_scalar_fold_v1 (value : IRTy -> IRStepResult) : IRByteConstFoldV1 :=
IRByteConstFoldV1.mk value (fun (_ : IRList IRTy) => IRStepResult.fault (IROutcome.type_error IRFault.bad_field))",
            r"def ir_byte_const_int_v1 (ctx : IRByteContextV1) (ty : IRTy) (word : Nat) : IRStepResult := match ty with
| IRTy.ptr_ => @Bool.rec (fun (_ : Bool) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) (IRStepResult.value IRScalar.nullptr_)
    (ir_nat_eqb word 0)
| _ => ir_byte_const_checked_v1 ctx ty (ir_byte_const_eval_v1 ty (IRConst.int_ word))",
            r"def ir_byte_const_prepend_v1 (head tail : IRStepResult) : IRStepResult := match head with
| IRStepResult.fault outcome => IRStepResult.fault outcome
| IRStepResult.value value => match tail with
  | IRStepResult.fault outcome => IRStepResult.fault outcome
  | IRStepResult.value spine => IRStepResult.value (IRScalar.vcons value spine)",
            r"def ir_byte_const_pack_v1 (result : IRStepResult) : IRStepResult := match result with
| IRStepResult.value spine => IRStepResult.value (IRScalar.aggv spine)
| IRStepResult.fault outcome => IRStepResult.fault outcome",
            r"def ir_byte_const_zero_second_v1 (spine : IRConst) : Bool := match spine with
| IRConst.vcons head tail => match head with
  | IRConst.int_ word => Bool.and (ir_nat_eqb word 0) (match tail with
    | IRConst.vnil => Bool.true
    | _ => Bool.false)
  | _ => Bool.false
| _ => Bool.false",
            r"def ir_byte_const_zero_fat_spine_v1 (spine : IRConst) : Bool := match spine with
| IRConst.vcons head tail => match head with
  | IRConst.int_ word => Bool.and (ir_nat_eqb word 0) (ir_byte_const_zero_second_v1 tail)
  | _ => Bool.false
| _ => Bool.false",
            r"def ir_byte_const_aggregate_v1 (ctx : IRByteContextV1) (spine : IRConst)
  (fields : IRList IRTy -> IRStepResult) (ty : IRTy) : IRStepResult := match ty with
| IRTy.struct_ id => @IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (fun (layout : IRByteLayoutV1) => ir_byte_const_checked_v1 ctx ty
      (ir_byte_const_pack_v1 (fields (ir_byte_layout_fields_v1 layout)))) (ir_byte_layout_v1 ctx ty)
| IRTy.enum_ id => @IROption.rec (IRList IRTy) (fun (_ : IROption (IRList IRTy)) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
    (fun (types : IRList IRTy) => ir_byte_const_checked_v1 ctx ty (ir_byte_const_pack_v1 (fields types)))
    (ir_byte_enum_spine_types_v1 ctx id (ir_const_value spine))
| _ => @IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult)
    (IRStepResult.fault (IROutcome.type_error IRFault.not_agg))
    (fun (_ : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult)
      (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
      (IRStepResult.value (IRScalar.fat_ 0 0)) (ir_byte_const_zero_fat_spine_v1 spine))
    (ir_byte_fat_metadata_ty_v1 ty)",
        ] {
            self.add_recursive_def(source, "Complete contextual SSA constant conversion; no byte-memory, layout, provider or source authority.")?;
        }
        let mut fold = String::from("def ir_byte_const_fold_v1 (ctx : IRByteContextV1) (constant : IRConst) : IRByteConstFoldV1 :=\n@IRConst.rec (fun (_ : IRConst) => IRByteConstFoldV1)\n");
        for (binders, value) in [
            ("(word : Nat)", "ir_byte_const_int_v1 ctx ty word"),
            (
                "(b : Bool)",
                "ir_byte_const_checked_v1 ctx ty (IRStepResult.value (IRScalar.bool_ b))",
            ),
            (
                "",
                "ir_byte_const_checked_v1 ctx ty (IRStepResult.value IRScalar.unit_)",
            ),
            (
                "",
                "ir_byte_const_checked_v1 ctx ty (IRStepResult.value IRScalar.nullptr_)",
            ),
            ("", BAD),
            (
                "(bits : Nat)",
                "ir_byte_const_checked_v1 ctx ty (IRStepResult.value (IRScalar.float_ bits))",
            ),
            (
                "(fid : Nat)",
                "ir_byte_const_checked_v1 ctx ty (IRStepResult.value (IRScalar.fnptr_ fid))",
            ),
        ] {
            if binders.is_empty() {
                fold.push_str(&format!(
                    "  (ir_byte_const_scalar_fold_v1 (fun (ty : IRTy) => {value}))\n"
                ));
            } else {
                fold.push_str(&format!("  (fun {binders} => ir_byte_const_scalar_fold_v1 (fun (ty : IRTy) => {value}))\n"));
            }
        }
        fold.push_str(&format!(
            "  (fun (spine : IRConst) (ih : IRByteConstFoldV1) => ir_byte_const_scalar_fold_v1\n    (ir_byte_const_aggregate_v1 ctx spine (ir_byte_const_fields_at_v1 ih)))\n  (IRByteConstFoldV1.mk (fun (_ : IRTy) => {BAD})\n    (fun (types : IRList IRTy) => match types with\n    | IRList.nil => IRStepResult.value IRScalar.vnil\n    | IRList.cons head tail => {BAD}))\n  (fun (_ : IRConst) (_ : IRConst) (head tail : IRByteConstFoldV1) =>\n    IRByteConstFoldV1.mk (fun (_ : IRTy) => {BAD})\n      (fun (types : IRList IRTy) => match types with\n      | IRList.nil => {BAD}\n      | IRList.cons ty rest => ir_byte_const_prepend_v1\n          (ir_byte_const_value_at_v1 head ty) (ir_byte_const_fields_at_v1 tail rest)))\n  (ir_byte_const_scalar_fold_v1 (fun (ty : IRTy) =>\n    ir_byte_const_checked_v1 ctx ty (IRStepResult.value IRScalar.unit_))) constant"
        ));
        self.add_recursive_def(&fold, "Joint structural constant recursion. Enum selection observes only the raw tag; all selected fields are converted recursively against their own types. Scalar/fat seeds are not opaque payload spines.")?;
        self.add_recursive_def(
            "def ir_byte_const_context_eval_v1 (ctx : IRByteContextV1) (ty : IRTy) (constant : IRConst) : IRStepResult := ir_byte_const_value_at_v1 (ir_byte_const_fold_v1 ctx constant) ty",
            "Actual ByteV1 Const dispatch evaluator. Complete contextual aggregates, canonical scalar lanes and zero-only opaque/fat seeds; no partial values or source certificate.",
        )?;
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_const_laws_v1(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &format!("def ir_byte_const_checked_input_v1 (ctx : IRByteContextV1) (ty : IRTy) (value : IRScalar)\n  (admitted : @Eq Bool (ir_byte_value_matches_v1 ctx ty value) Bool.true) :\n@Eq IRStepResult (ir_byte_const_checked_v1 ctx ty (IRStepResult.value value)) (IRStepResult.value value) :=\nir_byte_case_true_v1 IRStepResult (ir_byte_value_matches_v1 ctx ty value) ({BAD})\n  (IRStepResult.value value) (IRStepResult.value value) admitted (@Eq.refl IRStepResult (IRStepResult.value value))"),
            "Final constant admission guard from the existing structural type check, not an assumed Const result or source behavior.",
        )?;
        for source in [
            r"def ir_byte_const_fields_nil_v1 (ctx : IRByteContextV1) :
@Eq IRStepResult (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx IRConst.vnil) (@IRList.nil IRTy))
  (IRStepResult.value IRScalar.vnil) := @Eq.refl IRStepResult (IRStepResult.value IRScalar.vnil)",
            r"def ir_byte_const_fields_cons_v1 (ctx : IRByteContextV1) (head tail : IRConst)
  (ty : IRTy) (rest : IRList IRTy) (value spine : IRScalar)
  (first : @Eq IRStepResult (ir_byte_const_context_eval_v1 ctx ty head) (IRStepResult.value value))
  (remaining : @Eq IRStepResult (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx tail) rest) (IRStepResult.value spine)) :
@Eq IRStepResult (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx (IRConst.vcons head tail)) (@IRList.cons IRTy ty rest))
  (IRStepResult.value (IRScalar.vcons value spine)) :=
@Eq.trans IRStepResult
  (ir_byte_const_prepend_v1 (ir_byte_const_context_eval_v1 ctx ty head) (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx tail) rest))
  (ir_byte_const_prepend_v1 (IRStepResult.value value) (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx tail) rest))
  (IRStepResult.value (IRScalar.vcons value spine))
  (ir_eq_cong IRStepResult IRStepResult
    (fun (h : IRStepResult) => ir_byte_const_prepend_v1 h (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx tail) rest))
    (ir_byte_const_context_eval_v1 ctx ty head) (IRStepResult.value value) first)
  (ir_eq_cong IRStepResult IRStepResult (fun (t : IRStepResult) => ir_byte_const_prepend_v1 (IRStepResult.value value) t)
    (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 ctx tail) rest) (IRStepResult.value spine) remaining)",
            r"def ir_byte_const_zero_pointer_v1 (ctx : IRByteContextV1) :
@Eq IRStepResult (ir_byte_const_context_eval_v1 ctx IRTy.ptr_ (IRConst.int_ 0))
  (IRStepResult.value IRScalar.nullptr_) := @Eq.refl IRStepResult (IRStepResult.value IRScalar.nullptr_)",
        ] {
            self.add_recursive_def(source, "Structural contextual conversion equation; component premises preserve the actual recursive evaluator.")?;
        }
        for (name, ty, binders) in [
            ("fatstr", "IRTy.fatstr_", ""),
            ("fatslice", "IRTy.fatslice_ element", "(element : IRTy)"),
            ("fatdyn", "IRTy.fatdyn_ traitId", "(traitId : Nat)"),
            ("containerlen", "IRTy.containerlen_", ""),
            ("containervtable", "IRTy.containervtable_", ""),
        ] {
            self.add_recursive_def(
                &format!("def ir_byte_const_zero_{name}_v1 (ctx : IRByteContextV1) {binders} :\n@Eq IRStepResult (ir_byte_const_context_eval_v1 ctx ({ty}) ({ZERO_FAT}))\n  (IRStepResult.value (IRScalar.fat_ 0 0)) := @Eq.refl IRStepResult (IRStepResult.value (IRScalar.fat_ 0 0))"),
                "Exact two-zero seed at this nominal LE64 fat kind, not an arbitrary aggregate-to-pointer conversion or dereference right.",
            )?;
        }
        Ok(())
    }
}

// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use crate::spec::{SpecError, Specification};

pub(super) fn install(spec: &mut Specification) -> Result<(), SpecError> {
    for (name, source) in LAWS {
        spec.add_recursive_def(
            source,
            "Constructive complete-helper box law; no provider premise.",
        )?;
        spec.verify_definition(name)?;
    }
    Ok(())
}

const LAWS: &[(&str, &str)] = &[(
    "ir_clean_tag32_helper_box_v1",
    r"def ir_clean_tag32_helper_box_v1 (W : Type) (unbox : Nat) (boxer : Nat) (n : Nat) (mem : IRByteMemoryV1) (host : W) (bounded : Nat.lt n 4294967296) :
Eq (IRByteImportResultV1 W)
  (ir_clean_tag32_helper_provider_v1 W unbox boxer boxer (IRList.cons IRScalar (IRScalar.int_ n) (IRList.nil IRScalar)) mem host)
  (IRByteImportResultV1.mk W (IROutcome.ret (IRList.cons IRScalar (IRScalar.ptr_ (ir_clean_tag32_encode_v1 n)) (IRList.nil IRScalar))) mem host) :=
let bad : IRByteImportResultV1 W := IRByteImportResultV1.mk W (IROutcome.type_error IRFault.bad_field) mem host;
let result : IRByteImportResultV1 W := IRByteImportResultV1.mk W (IROutcome.ret (IRList.cons IRScalar (IRScalar.ptr_ (ir_clean_tag32_encode_v1 n)) (IRList.nil IRScalar))) mem host;
ir_byte_case_true_v1 (IRByteImportResultV1 W) (ir_nat_eqb boxer boxer)
  (ir_clean_tag32_provider_v1 W unbox boxer (IRList.cons IRScalar (IRScalar.int_ n) (IRList.nil IRScalar)) mem host)
  (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 W) bad result (ir_nat_ltb n 4294967296)) result
  (ir_byte_function_nat_eq_self_v1 boxer)
  (ir_byte_case_true_v1 (IRByteImportResultV1 W) (ir_nat_ltb n 4294967296) bad result result
    (ir_byte_ltb_of_lt_v1 n 4294967296 bounded) (Eq.refl (IRByteImportResultV1 W) result))",
)];

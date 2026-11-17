// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Quantified tag arithmetic and constructive provider law, reusing canonical
//! Euclidean arithmetic. These are not a complete helper or Rust refinement.
use crate::spec::{SpecError, Specification};

pub(super) fn install(spec: &mut Specification) -> Result<(), SpecError> {
    for (name, source) in LAWS {
        spec.add_recursive_def(
            source,
            "Quantified tag32 arithmetic/provider law; no provider equality assumption.",
        )?;
        spec.verify_definition(name)?;
    }
    Ok(())
}

const LAWS: &[(&str, &str)] = &[
    (
        "ir_clean_tag32_encode_v1",
        r"def ir_clean_tag32_encode_v1 (value : Nat) : Nat := Nat.add (Nat.mul value 2) 1",
    ),
    (
        "ir_clean_tag32_decode_encode_v1",
        r"def ir_clean_tag32_decode_encode_v1 (value : Nat) :
@Eq Nat (Nat.div (ir_clean_tag32_encode_v1 value) 2) value :=
ir_byte_div_unique_v1 (ir_clean_tag32_encode_v1 value) 2 value 1
  (@Nat.zero_lt_succ 1) (@Nat.succ_lt_succ 0 1 (@Nat.zero_lt_succ 0))
  (@Eq.refl Nat (ir_clean_tag32_encode_v1 value))",
    ),
    (
        "ir_clean_tag32_odd_encode_v1",
        r"def ir_clean_tag32_odd_encode_v1 (value : Nat) :
@Eq Nat (Nat.mod (ir_clean_tag32_encode_v1 value) 2) 1 :=
ir_byte_mod_unique_v1 (ir_clean_tag32_encode_v1 value) 2 value 1
  (@Nat.zero_lt_succ 1) (@Nat.succ_lt_succ 0 1 (@Nat.zero_lt_succ 0))
  (@Eq.refl Nat (ir_clean_tag32_encode_v1 value))",
    ),
    (
        "ir_clean_tag32_encoded_domain_v1",
        r"def ir_clean_tag32_encoded_domain_v1 (value : Nat) (bounded : Nat.lt value 4294967296) :
@Eq Bool (ir_clean_tag32_word_v1 (ir_clean_tag32_encode_v1 value)) Bool.true :=
@Eq.subst Nat
  (fun (decoded : Nat) => @Eq Bool (Bool.and (ir_nat_eqb (Nat.mod (ir_clean_tag32_encode_v1 value) 2) 1) (ir_nat_ltb decoded 4294967296)) Bool.true)
  value (Nat.div (ir_clean_tag32_encode_v1 value) 2)
  (@Eq.symm Nat (Nat.div (ir_clean_tag32_encode_v1 value) 2) value (ir_clean_tag32_decode_encode_v1 value))
  (@Eq.subst Nat
    (fun (remainder : Nat) => @Eq Bool (Bool.and (ir_nat_eqb remainder 1) (ir_nat_ltb value 4294967296)) Bool.true)
    1 (Nat.mod (ir_clean_tag32_encode_v1 value) 2)
    (@Eq.symm Nat (Nat.mod (ir_clean_tag32_encode_v1 value) 2) 1 (ir_clean_tag32_odd_encode_v1 value))
    (ir_byte_ltb_of_lt_v1 value 4294967296 bounded))",
    ),
    (
        "ir_clean_tag32_encoded_pointer_v1",
        r"def ir_clean_tag32_encoded_pointer_v1 (ctx : IRByteContextV1) (value : Nat) (bounded : Nat.lt value 4294967296) :
@Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ (IRScalar.ptr_ (ir_clean_tag32_encode_v1 value))) Bool.true :=
ir_byte_pointer_value_fits_v1 ctx (Nat.mul value 2)
  (@Eq.subst Nat (fun (predecessor : Nat) => Nat.lt (Nat.succ predecessor) ir_byte_limit_v1)
    (Nat.mul 2 value) (Nat.mul value 2) (@Nat.mul_comm 2 value)
    (@Nat.lt_trans (Nat.succ (Nat.mul 2 value)) 8589934593 ir_byte_limit_v1
      (@Nat.succ_lt_succ (Nat.mul 2 value) 8589934592 (@Nat.mul_lt_mul_left_succ 1 value 4294967296 bounded))
      (ir_byte_separation_lt_of_ltb_v1 8589934593 ir_byte_limit_v1 (@Eq.refl Bool Bool.true))))",
    ),
    (
        "ir_clean_tag32_provider_tagged_v1",
        r"def ir_clean_tag32_provider_tagged_v1
  (W : Type) (unbox : Nat) (word : Nat) (mem : IRByteMemoryV1) (host : W)
  (tagged : @Eq Bool (ir_clean_tag32_word_v1 word) Bool.true) :
@Eq (IRByteImportResultV1 W)
  (ir_clean_tag32_provider_v1 W unbox unbox (@IRList.cons IRScalar (IRScalar.ptr_ word) (@IRList.nil IRScalar)) mem host)
  (@IRByteImportResultV1.mk W (IROutcome.ret (@IRList.cons IRScalar (IRScalar.int_ (Nat.div word 2)) (@IRList.nil IRScalar))) mem host) :=
let bad : IRByteImportResultV1 W := @IRByteImportResultV1.mk W (IROutcome.type_error IRFault.bad_field) mem host;
let result : IRByteImportResultV1 W := @IRByteImportResultV1.mk W (IROutcome.ret (@IRList.cons IRScalar (IRScalar.int_ (Nat.div word 2)) (@IRList.nil IRScalar))) mem host;
ir_byte_case_true_v1 (IRByteImportResultV1 W) (ir_nat_eqb unbox unbox) bad
  (@Bool.rec (fun (_ : Bool) => IRByteImportResultV1 W) bad result (ir_clean_tag32_word_v1 word)) result
  (ir_byte_function_nat_eq_self_v1 unbox)
  (ir_byte_case_true_v1 (IRByteImportResultV1 W) (ir_clean_tag32_word_v1 word) bad result result tagged
    (@Eq.refl (IRByteImportResultV1 W) result))",
    ),
    (
        "ir_clean_tag32_provider_encoded_v1",
        r"def ir_clean_tag32_provider_encoded_v1
  (W : Type) (unbox : Nat) (value : Nat) (mem : IRByteMemoryV1) (host : W)
  (bounded : Nat.lt value 4294967296) :
@Eq (IRByteImportResultV1 W)
  (ir_clean_tag32_provider_v1 W unbox unbox (@IRList.cons IRScalar (IRScalar.ptr_ (ir_clean_tag32_encode_v1 value)) (@IRList.nil IRScalar)) mem host)
  (@IRByteImportResultV1.mk W (IROutcome.ret (@IRList.cons IRScalar (IRScalar.int_ value) (@IRList.nil IRScalar))) mem host) :=
@Eq.trans (IRByteImportResultV1 W)
  (ir_clean_tag32_provider_v1 W unbox unbox (@IRList.cons IRScalar (IRScalar.ptr_ (ir_clean_tag32_encode_v1 value)) (@IRList.nil IRScalar)) mem host)
  (@IRByteImportResultV1.mk W (IROutcome.ret (@IRList.cons IRScalar (IRScalar.int_ (Nat.div (ir_clean_tag32_encode_v1 value) 2)) (@IRList.nil IRScalar))) mem host)
  (@IRByteImportResultV1.mk W (IROutcome.ret (@IRList.cons IRScalar (IRScalar.int_ value) (@IRList.nil IRScalar))) mem host)
  (ir_clean_tag32_provider_tagged_v1 W unbox (ir_clean_tag32_encode_v1 value) mem host (ir_clean_tag32_encoded_domain_v1 value bounded))
  (ir_eq_cong Nat (IRByteImportResultV1 W)
    (fun (decoded : Nat) => @IRByteImportResultV1.mk W (IROutcome.ret (@IRList.cons IRScalar (IRScalar.int_ decoded) (@IRList.nil IRScalar))) mem host)
    (Nat.div (ir_clean_tag32_encode_v1 value) 2) value (ir_clean_tag32_decode_encode_v1 value))",
    ),
];

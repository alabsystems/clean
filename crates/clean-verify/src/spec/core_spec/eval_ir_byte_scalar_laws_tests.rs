// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel replay and refusal controls for the shared scalar laws.

use super::*;
use clean_kernel::Name;

fn spec() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("shared canonical byte vocabulary, including checked scalar laws")
}

fn assert_checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("registered checked term");
    assert!(!definition.is_axiom);
    assert!(definition.elaborated_value.is_some());
    spec.verify_definition(name).expect("kernel replay");
    let name = Name::from_string(name);
    assert!(spec
        .env()
        .axiom_deps(&name)
        .expect("root exists")
        .is_empty());
    assert!(spec
        .env()
        .trust_marker_deps(&name)
        .expect("root exists")
        .is_empty());
}

fn witness(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Kernel-checked scalar-law application")
        .expect("witness has a genuine proof term");
    assert_checked(spec, name);
}

fn reject_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid scalar-law application")
        .expect_err("the false range premise or conclusion must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn quantified_scalar_laws_check_without_axioms_or_trust_markers() {
    crate::test_utils::run_with_stack(|| {
        let spec = spec();
        for &(name, _) in LAWS {
            assert_checked(&spec, name);
        }
    });
}

#[test]
fn canonical_words_include_zero_and_the_signed_high_bit() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            (
                "byte_scalar_zero",
                "def byte_scalar_zero : @Eq Nat (ir_wrap 64 0) 0 := ir_byte_wrap_canonical_v1 64 0 (@Eq.refl Bool Bool.true)",
            ),
            (
                "byte_scalar_max_word",
                "def byte_scalar_max_word : @Eq Nat (ir_wrap 64 18446744073709551615) 18446744073709551615 := ir_byte_wrap_canonical_v1 64 18446744073709551615 (@Eq.refl Bool Bool.true)",
            ),
            (
                "byte_scalar_signed_word",
                "def byte_scalar_signed_word : @Eq Bool (ir_byte_integer_fits_v1 (IRTy.int_ 64) 18446744073709551615) Bool.true := ir_byte_i64_fits_v1 18446744073709551615 (@Eq.refl Bool Bool.true)",
            ),
            (
                "byte_scalar_zero_width",
                "def byte_scalar_zero_width : @Eq Nat (ir_wrap 0 0) 0 := ir_byte_wrap_canonical_v1 0 0 (@Eq.refl Bool Bool.true)",
            ),
        ] {
            witness(&mut spec, name, source);
        }
    });
}

#[test]
fn quantified_add_sub_laws_apply_at_wide_boundaries() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            ("byte_add_signed_high_bit", "def byte_add_signed_high_bit : @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.int_ 64) (IRScalar.int_ 9223372036854775807) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 9223372036854775808)) := ir_byte_add_int_below_v1 64 9223372036854775807 1 (@Eq.refl Bool Bool.true)"),
            ("byte_add_unsigned_zero", "def byte_add_unsigned_zero : @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.uint_ 32) (IRScalar.int_ 0) (IRScalar.int_ 0)) (IRStepResult.value (IRScalar.int_ 0)) := ir_byte_add_uint_below_v1 32 0 0 (@Eq.refl Bool Bool.true)"),
            ("byte_wrap_once_exact_modulus", "def byte_wrap_once_exact_modulus : @Eq Nat (ir_wrap 64 18446744073709551616) 0 := ir_byte_wrap_once_v1 64 18446744073709551615 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true)"),
            ("byte_wrap_once_above_modulus", "def byte_wrap_once_above_modulus : @Eq Nat (ir_wrap 128 340282366920938463463374607431768211457) 1 := ir_byte_wrap_once_v1 128 340282366920938463463374607431768211456 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true)"),
            ("byte_add_unsigned_wrap", "def byte_add_unsigned_wrap : @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.uint_ 64) (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 0)) := ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word)) (ir_wrap 64 18446744073709551616) 0 (ir_byte_wrap_once_v1 64 18446744073709551615 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true))"),
            ("byte_sub_unsigned_underflow", "def byte_sub_unsigned_underflow : @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.uint_ 64) (IRScalar.int_ 0) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 18446744073709551615)) := ir_byte_sub_uint_canonical_v1 64 0 1 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_sub_signed_underflow", "def byte_sub_signed_underflow : @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.int_ 32) (IRScalar.int_ 0) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 4294967295)) := ir_byte_sub_int_canonical_v1 32 0 1 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_sub_shared_operand", "def byte_sub_shared_operand : @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.uint_ 128) (IRScalar.int_ 17) (IRScalar.int_ 17)) (IRStepResult.value (IRScalar.int_ 0)) := ir_byte_sub_uint_canonical_v1 128 17 17 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
        ] {
            witness(&mut spec, name, source);
        }
    });
}

#[test]
fn quantified_add_sub_laws_reject_false_guards_and_wrong_answers() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            ("byte_add_false_no_wrap", "def byte_add_false_no_wrap : @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.uint_ 8) (IRScalar.int_ 255) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 256)) := ir_byte_add_uint_below_v1 8 255 1 (@Eq.refl Bool Bool.true)"),
            ("byte_wrap_false_once", "def byte_wrap_false_once : @Eq Nat (ir_wrap 8 512) 256 := ir_byte_wrap_once_v1 8 511 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true)"),
            ("byte_sub_false_canonical", "def byte_sub_false_canonical : @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.uint_ 8) (IRScalar.int_ 0) (IRScalar.int_ 256)) (IRStepResult.value (IRScalar.int_ 0)) := ir_byte_sub_uint_canonical_v1 8 0 256 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_sub_not_saturating", "def byte_sub_not_saturating : @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.uint_ 8) (IRScalar.int_ 0) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 0)) := ir_byte_sub_uint_canonical_v1 8 0 1 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_sub_not_add", "def byte_sub_not_add : @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.uint_ 8) (IRScalar.int_ 3) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 2)) := ir_byte_sub_uint_canonical_v1 8 3 1 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
        ] {
            reject_type_mismatch(&mut spec, name, source);
        }
    });
}

#[test]
fn zero_and_positive_status_tests_keep_actual_typed_icmp_semantics() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            (
                "byte_scalar_eq_zero",
                "def byte_scalar_eq_zero : @Eq IRStepResult (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ 64) (IRScalar.int_ 0) (IRScalar.int_ 0)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := ir_byte_icmp_uint_eq_zero_canonical_v1 64 0 (@Eq.refl Bool Bool.true)",
            ),
            (
                "byte_scalar_eq_max",
                "def byte_scalar_eq_max : @Eq IRStepResult (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ 64) (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 0)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := ir_byte_icmp_uint_eq_zero_positive_v1 64 18446744073709551614 (@Eq.refl Bool Bool.true)",
            ),
            (
                "byte_scalar_ne_max",
                "def byte_scalar_ne_max : @Eq IRStepResult (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ 64) (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 0)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := ir_byte_icmp_int_ne_zero_positive_v1 64 18446744073709551614 (@Eq.refl Bool Bool.true)",
            ),
        ] {
            witness(&mut spec, name, source);
        }
    });
}

#[test]
fn noncanonical_word_cannot_supply_the_range_premise() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        reject_type_mismatch(
            &mut spec,
            "byte_scalar_invalid_wrap",
            "def byte_scalar_invalid_wrap : @Eq Nat (ir_wrap 8 256) 256 := ir_byte_wrap_canonical_v1 8 256 (@Eq.refl Bool Bool.true)",
        );
        reject_type_mismatch(
            &mut spec,
            "byte_scalar_invalid_fit",
            "def byte_scalar_invalid_fit : @Eq Bool (ir_byte_integer_fits_v1 (IRTy.int_ 64) 18446744073709551616) Bool.true := ir_byte_i64_fits_v1 18446744073709551616 (@Eq.refl Bool Bool.true)",
        );
        reject_type_mismatch(
            &mut spec,
            "byte_scalar_invalid_guard",
            "def byte_scalar_invalid_guard : @Eq IRStepResult (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ 64) (IRScalar.int_ 1) (IRScalar.int_ 0)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := ir_byte_icmp_uint_eq_zero_positive_v1 64 0 (@Eq.refl Bool Bool.true)",
        );
    });
}

#[test]
fn canonical_comparisons_keep_both_open_operands_and_nonzero_answers() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (carrier, operator) in [("uint", "eq"), ("int", "eq"), ("uint", "ne"), ("int", "ne")] {
            let symbolic = if operator == "eq" {
                "ir_nat_eqb a b"
            } else {
                "Bool.not (ir_nat_eqb a b)"
            };
            let law = format!("ir_byte_icmp_{carrier}_{operator}_canonical_v1");
            let name = format!("byte_open_{carrier}_{operator}");
            witness(
                &mut spec,
                &name,
                &format!(
                    "def {name} (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.{operator}_ (IRTy.{carrier}_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ ({symbolic}))) := {law} width a b aFits bFits"
                ),
            );
            for (case, (left, right)) in [
                ("41", "41"),
                ("41", "53"),
                ("9223372036854775808", "9223372036854775808"),
                ("18446744073709551615", "9223372036854775808"),
            ]
            .into_iter()
            .enumerate()
            {
                let equal = left == right;
                let answer = if equal == (operator == "eq") {
                    "true"
                } else {
                    "false"
                };
                let name = format!("byte_nonzero_{carrier}_{operator}_{case}");
                witness(
                    &mut spec,
                    &name,
                    &format!(
                        "def {name} : @Eq IRStepResult
  (ir_byte_icmp_eval_v1 IRICmpOp.{operator}_ (IRTy.{carrier}_ 64) (IRScalar.int_ {left}) (IRScalar.int_ {right}))
  (IRStepResult.value (IRScalar.bool_ Bool.{answer})) := {law} 64 {left} {right}
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"
                    ),
                );
            }
        }
    });
}

#[test]
fn canonical_comparisons_reject_each_false_range_and_wrong_answer() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            ("byte_eq_bad_left", "def byte_eq_bad_left : @Eq IRStepResult (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ 8) (IRScalar.int_ 256) (IRScalar.int_ 7)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := ir_byte_icmp_uint_eq_canonical_v1 8 256 7 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_ne_bad_right", "def byte_ne_bad_right : @Eq IRStepResult (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ 8) (IRScalar.int_ 7) (IRScalar.int_ 256)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := ir_byte_icmp_int_ne_canonical_v1 8 7 256 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_eq_wrong_answer", "def byte_eq_wrong_answer : @Eq IRStepResult (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ 64) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := ir_byte_icmp_uint_eq_canonical_v1 64 41 53 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_ne_wrong_answer", "def byte_ne_wrong_answer : @Eq IRStepResult (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ 64) (IRScalar.int_ 41) (IRScalar.int_ 41)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := ir_byte_icmp_int_ne_canonical_v1 64 41 41 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_eq_wrong_rhs", "def byte_eq_wrong_rhs : @Eq IRStepResult (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ 64) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := ir_byte_icmp_uint_eq_canonical_v1 64 41 41 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
        ] {
            reject_type_mismatch(&mut spec, name, source);
        }
    });
}

#[test]
fn symbolic_select_preserves_exact_arms_and_actual_carriers() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            ("byte_select_open_values", "def byte_select_open_values (flag : Bool) (a b : IRScalar) : @Eq IRStepResult (ir_select_eval (IRScalar.bool_ flag) a b) (IRStepResult.value (@Bool.rec (fun (_ : Bool) => IRScalar) b a flag)) := ir_byte_select_eval_v1 flag a b"),
            ("byte_select_open_carriers", "def byte_select_open_carriers (ctx : IRByteContextV1) (ty : IRTy) (flag : Bool) (a b : IRScalar) (aFits : @Eq Bool (ir_byte_value_matches_v1 ctx ty a) Bool.true) (bFits : @Eq Bool (ir_byte_value_matches_v1 ctx ty b) Bool.true) : @Eq Bool (ir_byte_value_matches_v1 ctx ty (@Bool.rec (fun (_ : Bool) => IRScalar) b a flag)) Bool.true := ir_byte_select_value_fits_v1 ctx ty flag a b aFits bFits"),
            ("byte_select_open_words", "def byte_select_open_words (flag : Bool) (a b : Nat) : @Eq IRStepResult (ir_select_eval (IRScalar.bool_ flag) (IRScalar.int_ a) (IRScalar.int_ b)) (IRStepResult.value (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) b a flag))) := ir_byte_select_word_eval_v1 flag a b"),
            ("byte_select_open_word_bounds", "def byte_select_open_word_bounds (width : Nat) (flag : Bool) (a b : Nat) (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true) (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq Bool (ir_nat_ltb (@Bool.rec (fun (_ : Bool) => Nat) b a flag) (ir_nat_pow2 width)) Bool.true := ir_byte_select_word_bound_v1 width flag a b aFits bFits"),
            ("byte_select_true_arm", "def byte_select_true_arm : @Eq IRStepResult (ir_select_eval (IRScalar.bool_ Bool.true) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.int_ 41)) := ir_byte_select_word_eval_v1 Bool.true 41 53"),
            ("byte_select_false_arm", "def byte_select_false_arm : @Eq IRStepResult (ir_select_eval (IRScalar.bool_ Bool.false) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.int_ 53)) := ir_byte_select_word_eval_v1 Bool.false 41 53"),
            ("byte_select_carrier_context", "def byte_select_carrier_context : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)) (@IRList.nil IRByteLayoutV1) (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)"),
            ("byte_select_symbolic_uint_carrier", "def byte_select_symbolic_uint_carrier (flag : Bool) : @Eq Bool (ir_byte_value_matches_v1 byte_select_carrier_context (IRTy.uint_ 64) (@Bool.rec (fun (_ : Bool) => IRScalar) (IRScalar.int_ 53) (IRScalar.int_ 41) flag)) Bool.true := ir_byte_select_value_fits_v1 byte_select_carrier_context (IRTy.uint_ 64) flag (IRScalar.int_ 41) (IRScalar.int_ 53) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_select_symbolic_int_word", "def byte_select_symbolic_int_word (flag : Bool) : @Eq Bool (ir_byte_value_matches_v1 byte_select_carrier_context (IRTy.int_ 64) (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) 18446744073709551615 9223372036854775808 flag))) Bool.true := ir_byte_i64_value_fits_v1 byte_select_carrier_context (@Bool.rec (fun (_ : Bool) => Nat) 18446744073709551615 9223372036854775808 flag) (ir_byte_select_word_bound_v1 64 flag 9223372036854775808 18446744073709551615 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))"),
        ] {
            witness(&mut spec, name, source);
        }
    });
}

#[test]
fn symbolic_select_rejects_swapped_arms_nonbooleans_and_false_carriers() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, source) in [
            ("byte_select_swapped", "def byte_select_swapped (flag : Bool) : @Eq IRStepResult (ir_select_eval (IRScalar.bool_ flag) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) 41 53 flag))) := ir_byte_select_word_eval_v1 flag 41 53"),
            ("byte_select_nonboolean", "def byte_select_nonboolean : @Eq IRStepResult (ir_select_eval (IRScalar.int_ 1) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.int_ 41)) := ir_byte_select_word_eval_v1 Bool.true 41 53"),
            ("byte_select_wrong_arm", "def byte_select_wrong_arm : @Eq IRStepResult (ir_select_eval (IRScalar.bool_ Bool.false) (IRScalar.int_ 41) (IRScalar.int_ 53)) (IRStepResult.value (IRScalar.int_ 41)) := ir_byte_select_word_eval_v1 Bool.false 41 53"),
            ("byte_select_bad_left_bound", "def byte_select_bad_left_bound (flag : Bool) : @Eq Bool (ir_nat_ltb (@Bool.rec (fun (_ : Bool) => Nat) 7 256 flag) (ir_nat_pow2 8)) Bool.true := ir_byte_select_word_bound_v1 8 flag 256 7 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_select_bad_right_bound", "def byte_select_bad_right_bound (flag : Bool) : @Eq Bool (ir_nat_ltb (@Bool.rec (fun (_ : Bool) => Nat) 256 7 flag) (ir_nat_pow2 8)) Bool.true := ir_byte_select_word_bound_v1 8 flag 7 256 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
            ("byte_select_bad_carrier", "def byte_select_bad_carrier (ctx : IRByteContextV1) (flag : Bool) : @Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.uint_ 8) (@Bool.rec (fun (_ : Bool) => IRScalar) (IRScalar.bool_ Bool.true) (IRScalar.int_ 7) flag)) Bool.true := ir_byte_select_value_fits_v1 ctx (IRTy.uint_ 8) flag (IRScalar.int_ 7) (IRScalar.bool_ Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)"),
        ] {
            reject_type_mismatch(&mut spec, name, source);
        }
    });
}

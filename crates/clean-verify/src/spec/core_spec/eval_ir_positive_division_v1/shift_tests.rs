// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{install_shift_transactionally, shifts};
use crate::spec::SpecError;
use std::collections::BTreeSet;

#[cfg(test)]
#[path = "shift_test_support.rs"]
mod support;

use support::{
    certified, check_consumer, claim, collision, known_false_result_mismatch,
    known_false_type_mismatch, operation, owner_unchanged, positive,
    previous_definitions_unchanged, quotient, restoring_result, scalar_result, shifted, Shift,
    EXPECTED,
};

#[test]
fn shift_extension_adds_exact_eleven_actual_roots_without_changing_default_profiles() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(
            shifts::LAWS
                .iter()
                .map(|(name, _)| *name)
                .collect::<Vec<_>>(),
            EXPECTED
        );
        let byte = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("default ByteV1");
        let base = positive();
        let spec = shifted();
        assert_eq!(base.definitions().len(), byte.definitions().len() + 50);
        assert_eq!(spec.definitions().len(), base.definitions().len() + 11);
        assert_eq!(spec.definitions().len(), byte.definitions().len() + 61);
        let delta = spec.env().effect_since(base.env());
        let names: BTreeSet<_> = delta
            .changed_constant_names()
            .map(ToString::to_string)
            .collect();
        assert_eq!(
            names,
            EXPECTED
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>()
        );
        previous_definitions_unchanged(&byte, base);
        previous_definitions_unchanged(base, spec);
        for name in EXPECTED {
            certified(spec, name);
            assert!(byte.get_definition(name).is_none());
            assert!(base.get_definition(name).is_none());
        }
        for (name, _) in super::laws() {
            assert!(
                byte.get_definition(name).is_none(),
                "default ByteV1 must not install {name}"
            );
        }
        for (name, opcode, carrier) in [
            (
                "ir_byte_lshr_u64_by_three_v1",
                "IRBinOp.lshr",
                "IRTy.uint_ 64",
            ),
            (
                "ir_byte_ashr_i64_by_three_v1",
                "IRBinOp.ashr",
                "IRTy.int_ 64",
            ),
        ] {
            let source = &spec
                .get_definition(name)
                .expect("generic operation law")
                .type_src;
            for spelling in [
                "ir_binop_eval",
                opcode,
                carrier,
                "(word : Nat)",
                "ir_nat_pow2 64",
                "ir_dm_go 1 word 64 8",
            ] {
                assert!(source.contains(spelling), "{name} retains {spelling}");
            }
        }
        let later = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("default after extension");
        owner_unchanged(&byte, &later);
    });
}

#[test]
fn actual_generic_shift_consumers_cover_full_64_bit_boundaries_and_both_signs() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = shifted().clone();
        // Literal expected residues are independent of the restoring evaluator.
        for (word, logical, arithmetic) in [
            (0_u64, 0_u64, 0_u64),
            (7, 0, 0),
            (8, 1, 1),
            (
                9_223_372_036_854_775_807,
                1_152_921_504_606_846_975,
                1_152_921_504_606_846_975,
            ),
            (
                9_223_372_036_854_775_808,
                1_152_921_504_606_846_976,
                17_293_822_569_102_704_640,
            ),
            (
                18_446_744_073_709_551_608,
                2_305_843_009_213_693_951,
                18_446_744_073_709_551_615,
            ),
            (
                18_446_744_073_709_551_615,
                2_305_843_009_213_693_951,
                18_446_744_073_709_551_615,
            ),
        ] {
            for (shift, expected) in [(Shift::Logical, logical), (Shift::Arithmetic, arithmetic)] {
                let name = format!("shift_boundary_{}_{}", shift.opcode(), word);
                let source = claim(
                    &name,
                    shift,
                    word,
                    64,
                    3,
                    &scalar_result(&expected.to_string()),
                );
                check_consumer(&mut spec, &name, &source);
            }
        }
    });
}

#[test]
fn known_false_endpoints_fill_opcode_fuel_amount_and_width_have_unspent_type_mismatches() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = shifted().clone();
        let minimum = 9_223_372_036_854_775_808_u64;
        let q = quotient(&minimum.to_string(), 64);
        let fill_q = quotient("ir_nat_pow2 64", 64);
        let reversed_fill = scalar_result(&format!(
            "Nat.add ({q}) (Nat.sub ({fill_q}) (ir_nat_pow2 64))"
        ));
        let reversed_branch = scalar_result(&format!(
            "@Bool.rec (fun (_ : Bool) => Nat) (Nat.add ({q}) (Nat.sub (ir_nat_pow2 64) ({fill_q}))) ({q}) (ir_sign_bit 64 {minimum})"
        ));
        // Every mutant keeps the generic bridge first, so only the bounded
        // restoring side is normalized at large words. Amount/width mutations
        // use small inputs: their actual operation endpoints can also be read.
        for (case, shift, word, width, amount, wrong, actual_literal, wrong_literal) in [
            (
                "wrong_endpoint",
                Shift::Logical,
                8,
                64,
                3,
                scalar_result("0"),
                1,
                0,
            ),
            (
                "missing_fill",
                Shift::Arithmetic,
                minimum,
                64,
                3,
                scalar_result(&q),
                17_293_822_569_102_704_640,
                1_152_921_504_606_846_976,
            ),
            (
                "reversed_fill",
                Shift::Arithmetic,
                minimum,
                64,
                3,
                reversed_fill,
                17_293_822_569_102_704_640,
                1_152_921_504_606_846_976,
            ),
            (
                "reversed_sign_branch",
                Shift::Arithmetic,
                minimum,
                64,
                3,
                reversed_branch,
                17_293_822_569_102_704_640,
                1_152_921_504_606_846_976,
            ),
            // AShr -> Lshr at the high-bit -1 encoding, retaining AShr's answer.
            (
                "ashr_to_lshr",
                Shift::Logical,
                u64::MAX,
                64,
                3,
                scalar_result(&u64::MAX.to_string()),
                2_305_843_009_213_693_951,
                18_446_744_073_709_551_615,
            ),
            (
                "fuel_zero",
                Shift::Logical,
                8,
                64,
                3,
                scalar_result(&quotient("8", 0)),
                1,
                0,
            ),
            (
                "amount_four",
                Shift::Logical,
                8,
                64,
                4,
                scalar_result("1"),
                0,
                1,
            ),
            // Different width, not a signed/unsigned swap at equal width:
            // 256 wraps to 0 at width 8, but its width-64 quotient is 32.
            (
                "width_eight",
                Shift::Logical,
                256,
                8,
                3,
                scalar_result("32"),
                0,
                32,
            ),
        ] {
            let valid = format!("shift_mutation_control_{case}");
            let actual = operation(shift, word, width, amount);
            let correct = if width != 64 || amount != 3 {
                assert!(word <= 256, "direct actual endpoint probes stay small");
                actual.clone()
            } else {
                restoring_result(shift, word)
            };
            known_false_result_mismatch(
                &spec,
                case,
                &correct,
                &wrong,
                actual_literal,
                wrong_literal,
            );
            if width != 64 || amount != 3 {
                check_consumer(
                    &mut spec,
                    &valid,
                    &format!(
                        "def {valid} : @Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ 0)) := @Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 0))"
                    ),
                );
            } else {
                check_consumer(
                    &mut spec,
                    &valid,
                    &claim(&valid, shift, word, width, amount, &correct),
                );
            }
            let invalid = format!("shift_invalid_{case}");
            known_false_type_mismatch(
                &mut spec,
                &invalid,
                &claim(&invalid, shift, word, width, amount, &wrong),
            );
        }
    });
}

#[test]
fn shift_extension_early_late_and_repeat_collisions_preserve_the_owner() {
    crate::test_utils::run_with_stack(|| {
        for name in [EXPECTED[0], EXPECTED[10]] {
            let mut spec = positive().clone();
            spec.add_recursive_def(
                &format!("def {name} : Nat := Nat.zero"),
                "checked shift-name squatter",
            )
            .expect("squatter is type-correct");
            spec.env_mut()
                .set_option("shiftTest.sentinel".into(), Some("retained".into()));
            let before = spec.clone();
            collision(
                spec.install_eval_ir_u64_shift_by_three_laws_v1()
                    .expect_err("shift collision must refuse"),
                name,
            );
            owner_unchanged(&before, &spec);
        }
        let mut spec = shifted().clone();
        let before = spec.clone();
        collision(
            spec.install_eval_ir_u64_shift_by_three_laws_v1()
                .expect_err("repeat extension must refuse"),
            EXPECTED[0],
        );
        owner_unchanged(&before, &spec);
    });
}

#[test]
fn missing_positive_division_prerequisite_refuses_without_partial_shift_installation() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("default ByteV1 without positive division");
        assert!(spec.get_definition("ir_div_agrees_at_fuel").is_none());
        let before = spec.clone();
        let error = spec
            .install_eval_ir_u64_shift_by_three_laws_v1()
            .expect_err("the extension cannot invent its missing division agreement");
        assert!(
            error.to_string().contains("ir_div_agrees_at_fuel"),
            "{error}"
        );
        owner_unchanged(&before, &spec);
        assert!(EXPECTED
            .iter()
            .all(|name| spec.get_definition(name).is_none()));
    });
}

#[test]
fn eleventh_false_shift_source_rolls_back_the_entire_extension() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = positive().clone();
        let before = spec.clone();
        let mut rows = shifts::LAWS.to_vec();
        assert_eq!(rows.len(), 11);
        assert_eq!(rows[10].0, "ir_byte_ashr_i64_min_by_three_v1");
        rows[10].1 = "def ir_byte_ashr_i64_min_by_three_v1 : @Eq Nat Nat.zero (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)";
        let error = install_shift_transactionally(&mut spec, rows.into_iter())
            .expect_err("last false shift source must refuse after ten registrations");
        let detail = match error {
            SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
            other => panic!("late mathematical type mismatch required: {other}"),
        };
        assert!(
            detail.contains(EXPECTED[10]) && detail.to_ascii_lowercase().contains("type mismatch"),
            "{detail}"
        );
        owner_unchanged(&before, &spec);
        assert!(EXPECTED
            .iter()
            .all(|name| spec.get_definition(name).is_none()));
    });
}

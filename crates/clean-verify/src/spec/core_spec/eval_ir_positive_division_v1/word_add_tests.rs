// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::word_add;
use crate::spec::SpecError;
use std::collections::BTreeSet;

#[path = "word_add_tests_support.rs"]
mod support;
use support::*;

#[test]
fn bounded_add_installs_exact_checked_closure_without_default_or_evaluator_changes() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(
            word_add::LAWS
                .iter()
                .map(|(name, _)| *name)
                .collect::<Vec<_>>(),
            EXPECTED
        );
        let before = byte();
        let after = added();
        assert_eq!(
            after.definitions().len(),
            before.definitions().len() + EXPECTED.len()
        );
        let delta = after.env().effect_since(before.env());
        assert_eq!(
            delta
                .changed_constant_names()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
            EXPECTED
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>()
        );
        previous_definitions_unchanged(before, after);
        for name in EXPECTED {
            assert!(before.get_definition(name).is_none());
            certified(after, name);
        }
        assert!(before.get_definition("ir_div_agrees_at_fuel").is_none());
        assert!(before
            .get_definition("ir_byte_ashr_i64_in_range_v1")
            .is_none());
        let default = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        for name in EXPECTED {
            assert!(default.get_definition(name).is_none());
        }
        owner_unchanged(before, byte());
    });
}

#[test]
fn bounded_add_universal_actual_operations_derive_both_branches_and_canonical_results() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = added().clone();
        let selected = value("width", "a", "b");
        for carrier in ["uint_", "int_"] {
            let kind = if carrier == "uint_" { "uint" } else { "int" };
            let op = "ir_byte_add_".to_owned() + kind + "_canonical_v1";
            let bound = "ir_byte_add_".to_owned() + kind + "_canonical_result_bound_v1";
            let actual = format!("ir_binop_eval IRBinOp.add (IRTy.{carrier} width) (IRScalar.int_ a) (IRScalar.int_ b)");
            let name = format!("ordinary_bounded_add_{kind}");
            add_checked(&mut spec, &name, &format!(
                "def {name} (width a b : Nat) \
                 (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) : \
                 And (Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ ({selected})))) \
                   (Nat.lt ({selected}) (ir_nat_pow2 width)) := \
                 let aFits : Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true := ir_byte_ltb_of_lt_v1 a (ir_nat_pow2 width) aBound; \
                 let bFits : Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true := ir_byte_ltb_of_lt_v1 b (ir_nat_pow2 width) bBound; \
                 @And.intro (Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ ({selected})))) \
                   (Nat.lt ({selected}) (ir_nat_pow2 width)) ({op} width a b aFits bFits) \
                   (ir_byte_separation_lt_of_ltb_v1 ({selected}) (ir_nat_pow2 width) ({bound} width a b aFits bFits))"));
            for (label, flag, output) in [
                ("below", "true", "Nat.add a b"),
                (
                    "crossing",
                    "false",
                    "Nat.sub (Nat.add a b) (ir_nat_pow2 width)",
                ),
            ] {
                let name = format!("ordinary_bounded_add_{kind}_{label}");
                add_checked(&mut spec, &name, &format!(
                    "def {name} (width a b : Nat) \
                     (aFits : Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true) \
                     (bFits : Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) \
                     (branch : Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.{flag}) : \
                     Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ ({output}))) := \
                     Eq.trans IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ ({selected}))) \
                       (IRStepResult.value (IRScalar.int_ ({output}))) ({op} width a b aFits bFits) \
                       (ir_eq_cong Bool IRStepResult \
                         (fun (guard : Bool) => IRStepResult.value (IRScalar.int_ \
                           (Bool.rec (fun (_ : Bool) => Nat) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b) guard))) \
                         (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.{flag} branch)"));
            }
            let fit_law = if kind == "uint" {
                "ir_byte_u64_value_fits_v1"
            } else {
                "ir_byte_i64_value_fits_v1"
            };
            let result = value("64", "a", "b");
            let name = format!("ordinary_bounded_add_{kind}_full64_result_fits");
            add_checked(&mut spec, &name, &format!(
                "def {name} (ctx : IRByteContextV1) (a b : Nat) \
                 (aFits : Eq Bool (ir_nat_ltb a (ir_nat_pow2 64)) Bool.true) \
                 (bFits : Eq Bool (ir_nat_ltb b (ir_nat_pow2 64)) Bool.true) : \
                 Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.{carrier} 64) (IRScalar.int_ ({result}))) Bool.true := \
                 {fit_law} ctx ({result}) ({bound} 64 a b aFits bFits)"));
        }
    });
}

#[test]
fn bounded_add_full64_positive_negative_and_wrap_boundaries_match_independent_literals() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = added().clone();
        for (a, b) in [
            (0_u64, 0_u64),
            (1, 2),
            (i64::MAX as u64, 1),
            (i64::MIN as u64, i64::MIN as u64),
            (u64::MAX, 1),
            (u64::MAX, u64::MAX),
            (i64::MIN as u64, u64::MAX),
        ] {
            let expected = a.wrapping_add(b);
            let selected = value("64", &a.to_string(), &b.to_string());
            let residue = format!("independent_add_residue_{a}_{b}");
            add_checked(
                &mut spec,
                &residue,
                &format!(
                    "def {residue} : Eq Nat ({selected}) {expected} := Eq.refl Nat {expected}"
                ),
            );
            for carrier in ["uint_", "int_"] {
                let kind = if carrier == "uint_" { "uint" } else { "int" };
                let name = format!("full64_add_{kind}_{a}_{b}");
                let actual = operation(carrier, 64, a, b, "add");
                add_checked(&mut spec, &name, &format!(
                    "def {name} : Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ {expected})) := \
                     Eq.trans IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ ({selected}))) \
                       (IRStepResult.value (IRScalar.int_ {expected})) \
                       (ir_byte_add_{kind}_canonical_v1 64 {a} {b} (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)) \
                       (ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word)) \
                         ({selected}) {expected} {residue})"));
                let name = format!("{name}_result_bound");
                add_checked(&mut spec, &name, &format!(
                    "def {name} : Eq Bool (ir_nat_ltb ({selected}) (ir_nat_pow2 64)) Bool.true := \
                     ir_byte_add_{kind}_canonical_result_bound_v1 64 {a} {b} (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)"));
            }
        }
    });
}

#[test]
fn bounded_add_small_false_controls_refuse_changed_operands_width_opcode_and_answer() {
    crate::test_utils::run_with_stack(|| {
        let spec = added();
        for carrier in ["uint_", "int_"] {
            let kind = if carrier == "uint_" { "uint" } else { "int" };
            let selected = value("4", "14", "3");
            let original = operation(carrier, 4, 14, 3, "add");
            let proof = elaborate(spec, &format!(
                "Eq.trans IRStepResult ({original}) (IRStepResult.value (IRScalar.int_ ({selected}))) \
                   (IRStepResult.value (IRScalar.int_ 1)) \
                   (ir_byte_add_{kind}_canonical_v1 4 14 3 (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)) \
                   (Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 1)))"));
            for (actual, expected, false_answer) in [
                (operation(carrier, 4, 13, 3, "add"), 0, 1),
                (operation(carrier, 4, 14, 4, "add"), 2, 1),
                (operation(carrier, 5, 14, 3, "add"), 17, 1),
                (operation(carrier, 4, 14, 3, "mul"), 10, 1),
                (original.clone(), 1, 0),
            ] {
                let truth = elaborate(spec, &format!("Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ {expected}))"));
                let normal = elaborate(
                    spec,
                    &format!(
                        "Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ {expected}))"
                    ),
                );
                let tc = checker(spec);
                tc.check_type(&normal, &truth)
                    .expect("independent actual small normal form");
                unspent(&tc);
                let false_goal = elaborate(spec, &format!("Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ {false_answer}))"));
                rejects_false(spec, &proof, &false_goal);
            }
            let false_bound = elaborate(spec, "Eq Bool (ir_nat_ltb 16 (ir_nat_pow2 4)) Bool.true");
            let false_normal =
                elaborate(spec, "Eq Bool (ir_nat_ltb 16 (ir_nat_pow2 4)) Bool.false");
            let tc = checker(spec);
            tc.check_type(&elaborate(spec, "Eq.refl Bool Bool.false"), &false_normal)
                .unwrap();
            unspent(&tc);
            rejects_false(
                spec,
                &elaborate(spec, "Eq.refl Bool Bool.true"),
                &false_bound,
            );
        }
    });
}

#[test]
fn bounded_add_installer_refuses_every_collision_and_rolls_back_the_actual_last_false_law() {
    crate::test_utils::run_with_stack(|| {
        for name in EXPECTED {
            let mut spec = byte().clone();
            spec.add_recursive_def(
                &format!("def {name} : Nat := 0"),
                "ordinary collision control",
            )
            .unwrap();
            let before = spec.clone();
            let error = spec
                .install_eval_ir_bounded_add_laws_v1()
                .expect_err("occupied fixed name refuses");
            assert!(
                matches!(error, SpecError::EnvError(ref detail) if detail.contains("name collision") && detail.contains(name)),
                "{error}"
            );
            owner_unchanged(&before, &spec);
        }
        let mut spec = byte().clone();
        let before = spec.clone();
        const LAST: &str = "ir_byte_add_int_canonical_result_bound_v1";
        const FALSE_LAST: &str = "def ir_byte_add_int_canonical_result_bound_v1 : Eq Bool Bool.true Bool.false := Eq.refl Bool Bool.false";
        let rows = word_add::LAWS.iter().copied().map(|(name, source)| {
            if name == LAST {
                (name, FALSE_LAST)
            } else {
                (name, source)
            }
        });
        let error = word_add::install_transactionally(&mut spec, rows)
            .expect_err("late false law rolls back");
        let detail = match error {
            SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
            other => panic!("actual false final declaration needs typed refusal, got {other}"),
        };
        assert!(
            detail.contains(LAST),
            "must reach the actual last row: {detail}"
        );
        assert!(
            detail.to_ascii_lowercase().contains("type mismatch"),
            "{detail}"
        );
        for resource in [
            "budget",
            "heartbeat",
            "fuel exhausted",
            "depth limit",
            "parse error",
            "unknown identifier",
        ] {
            assert!(!detail.to_ascii_lowercase().contains(resource), "{detail}");
        }
        owner_unchanged(&before, &spec);
        for name in EXPECTED {
            assert!(spec.get_definition(name).is_none());
            assert!(spec
                .env()
                .get_const(&clean_kernel::Name::from_string(name))
                .is_none());
        }
    });
}

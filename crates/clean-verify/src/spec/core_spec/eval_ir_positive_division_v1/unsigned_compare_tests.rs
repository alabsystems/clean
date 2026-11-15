// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::unsigned_compare;
use crate::spec::SpecError;
use clean_kernel::{Declaration, Expr, Name, TypeError};
use std::collections::BTreeSet;

#[path = "unsigned_compare_tests_support.rs"]
mod support;
use support::*;

#[test]
fn unsigned_compare_exact_stored_root_closure_preserves_defaults_and_evaluators() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(
            unsigned_compare::LAWS
                .iter()
                .map(|(name, _)| *name)
                .collect::<Vec<_>>(),
            EXPECTED
        );
        assert_eq!(unsigned_compare::ROOTS, EXPECTED);
        let before = byte();
        let after = compared();
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
        assert!(after.get_definition("ir_div_agrees_at_fuel").is_none());
        assert!(after
            .get_definition("ir_byte_add_uint_canonical_v1")
            .is_none());
        let default = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        for name in EXPECTED {
            assert!(default.get_definition(name).is_none());
        }
        owner_unchanged(before, byte());
    });
}

#[test]
fn unsigned_compare_universal_actual_nominal_operations_and_boolean_result_fit() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = compared().clone();
        // Independently authored opcode/observer order, not producer-returned data.
        for (op, observer) in [
            ("ult", "ir_nat_ltb a b"),
            ("ule", "ir_nat_leb a b"),
            ("ugt", "ir_nat_ltb b a"),
            ("uge", "ir_nat_leb b a"),
        ] {
            for (carrier, kind) in [("uint_", "uint"), ("int_", "int")] {
                let operation = actual(carrier, "width", "a", "b", op);
                let result = format!("IRStepResult.value (IRScalar.bool_ ({observer}))");
                let law = format!("ir_byte_icmp_{kind}_{op}_canonical_v1");
                let authored_type = elaborate(&spec, &format!(
                    "forall (width a b : Nat) (aBound : Nat.lt a (ir_nat_pow2 width)) \
                     (bBound : Nat.lt b (ir_nat_pow2 width)), Eq IRStepResult ({operation}) ({result})"
                ));
                assert_eq!(
                    spec.env()
                        .get_const(&Name::from_string(&law))
                        .unwrap()
                        .type_,
                    authored_type,
                    "nominal carrier/opcode/operand/result must be structurally exact: {law}"
                );
                let name = format!("ordinary_unsigned_comparison_{kind}_{op}");
                add_checked(&mut spec, &name, &format!(
                    "def {name} (ctx : IRByteContextV1) (width a b : Nat) \
                     (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) : \
                     And (Eq IRStepResult ({operation}) ({result})) \
                       (Eq Bool (ir_byte_value_matches_v1 ctx IRTy.bool_ (IRScalar.bool_ ({observer}))) Bool.true) := \
                     @And.intro (Eq IRStepResult ({operation}) ({result})) \
                       (Eq Bool (ir_byte_value_matches_v1 ctx IRTy.bool_ (IRScalar.bool_ ({observer}))) Bool.true) \
                       ({law} width a b aBound bBound) (Eq.refl Bool Bool.true)"
                ));
            }
        }
    });
}

#[test]
fn unsigned_compare_full64_negative_encodings_and_zero_width_match_independent_observers() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = compared().clone();
        // Width zero is an evaluator law with sole canonical word zero, not a
        // claim that ByteV1 accepts zero-width integer argument carriers.
        for (width, a, b) in [
            (0_u64, 0_u64, 0_u64),
            (1, 0, 1),
            (1, 1, 0),
            (64, 0, 0),
            (64, 1_u64 << 31, 1_u64 << 32),
            (64, 1_u64 << 32, 1_u64 << 31),
            (64, i64::MIN as u64, i64::MAX as u64),
            (64, i64::MAX as u64, i64::MIN as u64),
            (64, u64::MAX, u64::MAX),
            (64, u64::MAX, 0),
        ] {
            let width = width.to_string();
            let a_text = a.to_string();
            let b_text = b.to_string();
            // All four observers receive full-width equality/ordering cases;
            // Uge additionally covers every TLC32/sign boundary above.
            for op in ["ult", "ule", "ugt", "uge"] {
                if op != "uge" && !(a == b || (width == "64" && a == i64::MIN as u64)) {
                    continue;
                }
                let (predicate, left, right, expected) = match op {
                    "ult" => ("ir_nat_ltb", a, b, a < b),
                    "ule" => ("ir_nat_leb", a, b, a <= b),
                    "ugt" => ("ir_nat_ltb", b, a, a > b),
                    "uge" => ("ir_nat_leb", b, a, a >= b),
                    _ => unreachable!("fixed test opcode inventory"),
                };
                let flag = if expected { "true" } else { "false" };
                let observer = format!("{predicate} {left} {right}");
                let observed = format!("independent_comparison_{op}_{width}_{a}_{b}");
                // Fold only the original unwrapped observer, never ir_wrap on
                // full64 operands or the whole actual operation by reflexivity.
                add_checked(
                    &mut spec,
                    &observed,
                    &format!(
                    "def {observed} : Eq Bool ({observer}) Bool.{flag} := Eq.refl Bool Bool.{flag}"
                ),
                );
                for (carrier, kind) in [("uint_", "uint"), ("int_", "int")] {
                    let operation = actual(carrier, &width, &a_text, &b_text, op);
                    let name = format!("full_width_comparison_{kind}_{op}_{width}_{a}_{b}");
                    add_checked(&mut spec, &name, &format!(
                        "def {name} : Eq IRStepResult ({operation}) (IRStepResult.value (IRScalar.bool_ Bool.{flag})) := \
                         Eq.trans IRStepResult ({operation}) (IRStepResult.value (IRScalar.bool_ ({observer}))) \
                           (IRStepResult.value (IRScalar.bool_ Bool.{flag})) \
                           (ir_byte_icmp_{kind}_{op}_canonical_v1 {width} {a} {b} ({}) ({})) \
                           (ir_eq_cong Bool IRStepResult (fun (answer : Bool) => IRStepResult.value (IRScalar.bool_ answer)) \
                             ({observer}) Bool.{flag} {observed})",
                        bound(&width, &a_text), bound(&width, &b_text)
                    ));
                }
            }
        }
    });
}

#[test]
fn unsigned_compare_actual_false_uge_controls_reject_operands_opcode_width_and_answer() {
    crate::test_utils::run_with_stack(|| {
        let spec = compared();
        for (carrier, kind) in [("uint_", "uint"), ("int_", "int")] {
            let original = actual(carrier, "4", "8", "8", "uge");
            let proof = elaborate(spec, &format!(
                "Eq.trans IRStepResult ({original}) (IRStepResult.value (IRScalar.bool_ (ir_nat_leb 8 8))) \
                  (IRStepResult.value (IRScalar.bool_ Bool.true)) \
                  (ir_byte_icmp_{kind}_uge_canonical_v1 4 8 8 ({0}) ({0})) \
                  (Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true)))", bound("4", "8")
            ));
            for (operation, expected, false_answer) in [
                (actual(carrier, "4", "7", "8", "uge"), "false", "true"),
                (actual(carrier, "4", "8", "9", "uge"), "false", "true"),
                (actual(carrier, "4", "8", "8", "ugt"), "false", "true"),
                (original, "true", "false"),
            ] {
                let truth = elaborate(spec, &format!("Eq IRStepResult ({operation}) (IRStepResult.value (IRScalar.bool_ Bool.{expected}))"));
                let normal = elaborate(spec, &format!("Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.{expected}))"));
                let tc = checker(spec);
                tc.check_type(&normal, &truth)
                    .expect("independent actual small normal form");
                unspent(&tc);
                let false_goal = elaborate(spec, &format!("Eq IRStepResult ({operation}) (IRStepResult.value (IRScalar.bool_ Bool.{false_answer}))"));
                rejects_false(spec, &proof, &false_goal);
            }
            let original = actual(carrier, "4", "8", "3", "uge");
            let proof = elaborate(spec, &format!(
                "Eq.trans IRStepResult ({original}) (IRStepResult.value (IRScalar.bool_ (ir_nat_leb 3 8))) \
                  (IRStepResult.value (IRScalar.bool_ Bool.true)) \
                  (ir_byte_icmp_{kind}_uge_canonical_v1 4 8 3 ({}) ({})) \
                  (Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true)))", bound("4", "8"), bound("4", "3")
            ));
            // A real changed-width operation: width3 wraps eight to zero.
            for operation in [
                actual(carrier, "3", "8", "3", "uge"),
                actual(carrier, "4", "3", "8", "uge"),
            ] {
                let truth = elaborate(spec, &format!("Eq IRStepResult ({operation}) (IRStepResult.value (IRScalar.bool_ Bool.false))"));
                let tc = checker(spec);
                tc.check_type(
                    &elaborate(
                        spec,
                        "Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))",
                    ),
                    &truth,
                )
                .expect("independently normalizing the changed width/swapped operands");
                unspent(&tc);
                let false_goal = elaborate(spec, &format!("Eq IRStepResult ({operation}) (IRStepResult.value (IRScalar.bool_ Bool.true))"));
                rejects_false(spec, &proof, &false_goal);
            }
            let ill_typed = Expr::apps(
                elaborate(spec, &format!("ir_byte_icmp_{kind}_uge_canonical_v1")),
                [
                    elaborate(spec, "4"),
                    elaborate(spec, "16"),
                    elaborate(spec, "3"),
                    elaborate(spec, &bound("4", "15")),
                    elaborate(spec, &bound("4", "3")),
                ],
            );
            let tc = checker(spec);
            tc.check_type(
                &elaborate(spec, "Eq.refl Bool Bool.false"),
                &elaborate(spec, "Eq Bool (ir_nat_ltb 16 (ir_nat_pow2 4)) Bool.false"),
            )
            .expect("independently, sixteen is not canonical at width4");
            // Full check mode validates every application argument. The
            // infer-only fast path deliberately omits those release checks.
            let error = tc
                .infer_type_full(&ill_typed)
                .expect_err("another word's canonical bound cannot prove sixteen fits width4");
            assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error}");
            assert_eq!(tc.local_context_len(), 0, "refusal is context-neutral");
            unspent(&tc);
        }
    });
}

#[test]
fn unsigned_compare_atomic_collisions_and_actual_last_false_row_refuse_without_authority() {
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
                .install_eval_ir_unsigned_compare_laws_v1_checked()
                .expect_err("occupied name refuses");
            assert!(
                matches!(error, SpecError::EnvError(ref detail) if detail.contains("name collision") && detail.contains(name)),
                "{error}"
            );
            owner_unchanged(&before, &spec);
        }
        let mut spec = byte().clone();
        const LAST: &str = "ir_byte_icmp_int_uge_canonical_v1";
        spec.env_mut()
            .add_decl(Declaration::Axiom {
                name: Name::from_string(LAST),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
            })
            .expect("deliberate environment-only occupied name");
        let before = spec.clone();
        assert!(spec.get_definition(LAST).is_none());
        let error = spec
            .install_eval_ir_unsigned_compare_laws_v1_checked()
            .expect_err("environment-only name refuses");
        assert!(
            matches!(error, SpecError::EnvError(ref detail) if detail.contains("name collision") && detail.contains(LAST)),
            "{error}"
        );
        owner_unchanged(&before, &spec);

        let mut spec = byte().clone();
        let before = spec.clone();
        const FALSE_LAST: &str = "def ir_byte_icmp_int_uge_canonical_v1 : Eq Bool Bool.true Bool.false := Eq.refl Bool Bool.false";
        let rows = unsigned_compare::LAWS
            .iter()
            .copied()
            .map(|(name, source)| {
                if name == LAST {
                    (name, FALSE_LAST)
                } else {
                    (name, source)
                }
            });
        let error = unsigned_compare::install_transactionally(&mut spec, rows)
            .expect_err("actual false last row rolls back");
        let detail = match error {
            SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
            other => panic!("last mathematical falsehood needs typed refusal: {other}"),
        };
        assert!(
            detail.contains(LAST),
            "must reach actual last row: {detail}"
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
            assert!(spec.env().get_const(&Name::from_string(name)).is_none());
        }
    });
}

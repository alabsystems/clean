// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Replay the actual fetched Copy/Return dispatcher with complete final worlds.
//! These model tests do not supply source validation or native memory authority.

use super::{check, context, machine_spec, register, returned, run, Function, Node};

fn halted(value: &str, host: u64) -> String {
    format!("@IRByteConfigV1.halted Nat ({}) (@IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 byte_machine_external_mem) {host} (@IRList.nil Nat) 2)", returned(&[value]))
}

fn fault(host: u64) -> String {
    format!("@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) (@IRByteWorldV1.mk Nat byte_machine_external_mem {host} (@IRList.cons Nat 1 (@IRList.nil Nat)) 2)")
}

#[test]
fn byte_copy_machine_replays_canonical_carriers_and_entire_returned_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (case, (ty, value)) in [
            ("IRTy.int_ 8", "IRScalar.int_ 255"),
            ("IRTy.uint_ 13", "IRScalar.int_ 8191"),
            ("IRTy.int_ 64", "IRScalar.int_ 9223372036854775808"),
            ("IRTy.uint_ 64", "IRScalar.int_ 18446744073709551615"),
            ("IRTy.bool_", "IRScalar.bool_ Bool.false"),
            ("IRTy.bool_", "IRScalar.bool_ Bool.true"),
            // 128 is not in the fixture's allocation. Copy is not a load.
            ("IRTy.ptr_", "IRScalar.ptr_ 128"),
            ("IRTy.ptr_", "IRScalar.nullptr_"),
            ("IRTy.refmut_ (IRTy.int_ 64)", "IRScalar.ptr_ 128"),
            ("IRTy.unit_", "IRScalar.unit_"),
            ("IRTy.func_ 41", "IRScalar.fnptr_ 41"),
            ("IRTy.struct_ 9", "IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 18446744073709551615) (IRScalar.vcons (IRScalar.int_ 9223372036854775808) IRScalar.vnil))"),
        ].into_iter().enumerate() {
            let ctx = format!("byte_copy_context_{case}");
            context(&mut spec, &ctx, &[Function::local(41, &[ty], &[ty], vec![
                Node::new(format!("IRInst.copy ({ty}) 0"), &[99], &[ty]),
                Node::ret(&[99]),
            ])]);
            let actual = run(&ctx, "byte_machine_no_import", 41, &[value],
                "byte_machine_external_mem", 73, 2);
            check(&mut spec, &format!("byte_copy_complete_{case}"), "IRByteConfigV1 Nat",
                &actual, &halted(value, 73));
        }
    });
}

#[test]
fn byte_copy_machine_checks_width_carrier_and_actual_result_metadata() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        // Every root argument is admitted. Each refusal happens at the Copy
        // or its actual result binding, rather than at entry initialization.
        for (case, (source_ty, copy_ty, value, results, result_types)) in [
            (
                "IRTy.uint_ 64",
                "IRTy.uint_ 8",
                "IRScalar.int_ 256",
                vec![99],
                vec!["IRTy.uint_ 8"],
            ),
            (
                "IRTy.bool_",
                "IRTy.uint_ 64",
                "IRScalar.bool_ Bool.true",
                vec![99],
                vec!["IRTy.uint_ 64"],
            ),
            (
                "IRTy.ptr_",
                "IRTy.uint_ 64",
                "IRScalar.ptr_ 128",
                vec![99],
                vec!["IRTy.uint_ 64"],
            ),
            (
                "IRTy.uint_ 64",
                "IRTy.ptr_",
                "IRScalar.int_ 128",
                vec![99],
                vec!["IRTy.ptr_"],
            ),
            (
                "IRTy.uint_ 64",
                "IRTy.uint_ 64",
                "IRScalar.int_ 3",
                vec![99],
                vec!["IRTy.ptr_"],
            ),
            (
                "IRTy.uint_ 64",
                "IRTy.uint_ 64",
                "IRScalar.int_ 3",
                vec![],
                vec![],
            ),
            (
                "IRTy.uint_ 64",
                "IRTy.uint_ 64",
                "IRScalar.int_ 3",
                vec![99, 100],
                vec!["IRTy.uint_ 64", "IRTy.uint_ 64"],
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = format!("byte_copy_bad_context_{case}");
            context(
                &mut spec,
                &ctx,
                &[Function::local(
                    41,
                    &[source_ty],
                    &[],
                    vec![
                        Node::new(
                            format!("IRInst.copy ({copy_ty}) 0"),
                            &results,
                            &result_types,
                        ),
                        Node::ret(&[]),
                    ],
                )],
            );
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                41,
                &[value],
                "byte_machine_external_mem",
                19,
                2,
            );
            check(
                &mut spec,
                &format!("byte_copy_fault_{case}"),
                "IRByteConfigV1 Nat",
                &actual,
                &fault(19),
            );
        }
    });
}

#[test]
fn byte_copy_machine_advances_once_and_rejects_stale_whole_claims() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        context(
            &mut spec,
            "byte_copy_resume_ctx",
            &[Function::local(
                41,
                &["IRTy.uint_ 64", "IRTy.uint_ 64"],
                &["IRTy.uint_ 64"],
                vec![
                    Node::new("IRInst.copy (IRTy.uint_ 64) 1", &[99], &["IRTy.uint_ 64"]),
                    Node::ret(&[99]),
                ],
            )],
        );
        let first = run(
            "byte_copy_resume_ctx",
            "byte_machine_no_import",
            41,
            &["IRScalar.int_ 3", "IRScalar.int_ 7"],
            "byte_machine_external_mem",
            37,
            1,
        );
        let resumed =
            format!("ir_byte_run_v1 Nat byte_copy_resume_ctx byte_machine_no_import 1 ({first})");
        check(
            &mut spec,
            "byte_copy_resumed_whole",
            "IRByteConfigV1 Nat",
            &resumed,
            &halted("IRScalar.int_ 7", 37),
        );
        register(&mut spec, "def byte_copy_direct_valid : @Eq (IRStepResult) (ir_byte_copy_eval_v1 byte_copy_resume_ctx (IRTy.uint_ 64) (IRScalar.int_ 7)) (IRStepResult.value (IRScalar.int_ 7)) := @Eq.refl (IRStepResult) (IRStepResult.value (IRScalar.int_ 7))");
        for (case, expected) in [
            halted("IRScalar.int_ 3", 37),
            halted("IRScalar.int_ 7", 38),
            fault(37),
        ]
        .into_iter()
        .enumerate()
        {
            let result = spec.add_recursive_def(
                &format!("def byte_copy_stale_{case} : @Eq (IRByteConfigV1 Nat) ({resumed}) ({expected}) := byte_copy_resumed_whole"),
                "Deliberately stale Copy proof must not establish changed complete endpoints");
            let error = result
                .expect_err("stale whole-claim proof must fail")
                .to_string();
            for resource in [
                "heartbeat",
                "budget",
                "timeout",
                "fuel exhausted",
                "recursion limit",
            ] {
                assert!(!error.to_lowercase().contains(resource), "{error}");
            }
        }
    });
}

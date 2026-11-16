// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scalar-operation fixtures for the byte machine; shared builders and checks
//! remain private in the parent test module.

use super::{check, context, machine_spec, outcome, returned, run, world, Function, Node};

#[test]
fn byte_add_sub_machine_canonical_words_wrap_and_return() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        // The byte target is 64-bit, but canonical integer carriers retain
        // the existing 1..=128 width domain, including non-power-of-two widths.
        for (case, (ty, left, right, sum, difference)) in [
            ("IRTy.uint_ 1", "1", "1", "0", "0"),
            ("IRTy.int_ 8", "0", "1", "1", "255"),
            ("IRTy.uint_ 13", "8191", "1", "0", "8190"),
            ("IRTy.uint_ 32", "4294967295", "1", "0", "4294967294"),
            (
                "IRTy.int_ 32",
                "2147483647",
                "1",
                "2147483648",
                "2147483646",
            ),
            (
                "IRTy.uint_ 64",
                "18446744073709551615",
                "1",
                "0",
                "18446744073709551614",
            ),
            (
                "IRTy.int_ 64",
                "9223372036854775808",
                "1",
                "9223372036854775809",
                "9223372036854775807",
            ),
            (
                "IRTy.uint_ 128",
                "340282366920938463463374607431768211455",
                "1",
                "0",
                "340282366920938463463374607431768211454",
            ),
            (
                "IRTy.int_ 128",
                "0",
                "1",
                "1",
                "340282366920938463463374607431768211455",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let root = Function::local(
                41,
                &[ty, ty],
                &[ty, ty, ty],
                vec![
                    Node::new(format!("IRInst.binop IRBinOp.add ({ty}) 0 1"), &[99], &[ty]),
                    Node::new(
                        format!("IRInst.binop IRBinOp.sub ({ty}) 0 1"),
                        &[300],
                        &[ty],
                    ),
                    Node::new(
                        format!("IRInst.binop IRBinOp.sub ({ty}) 0 0"),
                        &[901],
                        &[ty],
                    ),
                    Node::ret(&[300, 99, 901]),
                ],
            );
            let ctx = format!("byte_arithmetic_context_{case}");
            context(&mut spec, &ctx, &[root]);
            let args = [
                format!("IRScalar.int_ {left}"),
                format!("IRScalar.int_ {right}"),
            ];
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                41,
                &[&args[0], &args[1]],
                "byte_machine_external_mem",
                73,
                4,
            );
            let expected = returned(&[
                &format!("IRScalar.int_ {difference}"),
                &format!("IRScalar.int_ {sum}"),
                "IRScalar.int_ 0",
            ]);
            check(
                &mut spec,
                &format!("byte_arithmetic_return_{case}"),
                "IROutcome",
                &outcome(&actual),
                &expected,
            );
            // Initialization creates owner 1; Return retires it and keeps the
            // external allocation, host state and exact next-owner counter.
            check(&mut spec, &format!("byte_arithmetic_world_{case}"), "IRByteWorldV1 Nat", &world(&actual),
                "@IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 byte_machine_external_mem) 73 (@IRList.nil Nat) 2");
        }
    });
}

#[test]
fn byte_add_sub_machine_fuel_stops_before_return() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        context(
            &mut spec,
            "byte_arithmetic_fuel_context",
            &[Function::local(
                17,
                &["IRTy.uint_ 64", "IRTy.uint_ 64"],
                &["IRTy.uint_ 64"],
                vec![
                    Node::new(
                        "IRInst.binop IRBinOp.sub (IRTy.uint_ 64) 0 1",
                        &[99],
                        &["IRTy.uint_ 64"],
                    ),
                    Node::ret(&[99]),
                ],
            )],
        );
        let actual = run(
            "byte_arithmetic_fuel_context",
            "byte_machine_no_import",
            17,
            &["IRScalar.int_ 0", "IRScalar.int_ 1"],
            "byte_machine_external_mem",
            19,
            1,
        );
        check(&mut spec, "byte_arithmetic_one_step_world", "IRByteWorldV1 Nat", &world(&actual),
            "@IRByteWorldV1.mk Nat byte_machine_external_mem 19 (@IRList.cons Nat 1 (@IRList.nil Nat)) 2");
        let resumed = format!(
            "ir_byte_run_v1 Nat byte_arithmetic_fuel_context byte_machine_no_import 1 ({actual})"
        );
        check(
            &mut spec,
            "byte_arithmetic_resumed_return",
            "IROutcome",
            &outcome(&resumed),
            &returned(&["IRScalar.int_ 18446744073709551615"]),
        );
    });
}

#[test]
fn byte_binop_machine_uses_the_existing_integer_operator_contract() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (case, (op, left, right, value)) in [
            ("add", 10, 3, 13),
            ("sub", 10, 3, 7),
            ("mul", 10, 3, 14),
            ("udiv", 10, 3, 3),
            ("sdiv", 13, 2, 15),
            ("urem", 10, 3, 1),
            ("srem", 13, 2, 15),
            ("and_", 10, 3, 2),
            ("or_", 10, 3, 11),
            ("xor_", 10, 3, 9),
            ("shl", 10, 3, 0),
            ("lshr", 10, 3, 1),
            ("ashr", 13, 2, 15),
        ]
        .into_iter()
        .enumerate()
        {
            let ty = "IRTy.int_ 4";
            let ctx = format!("byte_integer_binop_context_{case}");
            context(
                &mut spec,
                &ctx,
                &[Function::local(
                    17,
                    &[ty, ty],
                    &[ty],
                    vec![
                        Node::new(
                            format!("IRInst.binop IRBinOp.{op} ({ty}) 0 1"),
                            &[99],
                            &[ty],
                        ),
                        Node::ret(&[99]),
                    ],
                )],
            );
            let args = [
                format!("IRScalar.int_ {left}"),
                format!("IRScalar.int_ {right}"),
            ];
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                17,
                &[&args[0], &args[1]],
                "byte_machine_external_mem",
                29,
                2,
            );
            check(
                &mut spec,
                &format!("byte_integer_binop_result_{case}"),
                "IROutcome",
                &outcome(&actual),
                &returned(&[&format!("IRScalar.int_ {value}")]),
            );
        }
        // These are kernel reductions of canonical execution, not quantified
        // proof-builder coverage or a new fast-arithmetic implementation.
    });
}

#[test]
fn byte_binop_machine_boolean_and_opcode_signedness_contract() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for op in ["and_", "or_", "xor_"] {
            for left in [false, true] {
                for right in [false, true] {
                    let value = match op {
                        "and_" => left && right,
                        "or_" => left || right,
                        _ => left != right,
                    };
                    let scalar = |v| {
                        if v {
                            "IRScalar.bool_ Bool.true"
                        } else {
                            "IRScalar.bool_ Bool.false"
                        }
                    };
                    let ctx = format!("byte_boolean_{op}_{left}_{right}");
                    context(
                        &mut spec,
                        &ctx,
                        &[Function::local(
                            17,
                            &["IRTy.bool_", "IRTy.bool_"],
                            &["IRTy.bool_"],
                            vec![
                                Node::new(
                                    format!("IRInst.binop IRBinOp.{op} IRTy.bool_ 0 1"),
                                    &[99],
                                    &["IRTy.bool_"],
                                ),
                                Node::ret(&[99]),
                            ],
                        )],
                    );
                    let actual = run(
                        &ctx,
                        "byte_machine_no_import",
                        17,
                        &[scalar(left), scalar(right)],
                        "byte_machine_external_mem",
                        29,
                        2,
                    );
                    check(
                        &mut spec,
                        &format!("{ctx}_result"),
                        "IROutcome",
                        &outcome(&actual),
                        &returned(&[scalar(value)]),
                    );
                    check(&mut spec, &format!("{ctx}_world"), "IRByteWorldV1 Nat", &world(&actual),
                        "@IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 byte_machine_external_mem) 29 (@IRList.nil Nat) 2");
                }
            }
        }
        // Signedness belongs to the opcode, not the declared carrier tag.
        // These cases deliberately use the other declaration's high bit.
        for (case, (ty, op, expected)) in [
            ("IRTy.uint_ 4", "sdiv", 15),
            ("IRTy.uint_ 4", "srem", 15),
            ("IRTy.uint_ 4", "ashr", 15),
            ("IRTy.int_ 4", "udiv", 6),
            ("IRTy.int_ 4", "urem", 1),
            ("IRTy.int_ 4", "lshr", 3),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = format!("byte_cross_signedness_{case}");
            context(
                &mut spec,
                &ctx,
                &[Function::local(
                    17,
                    &[ty, ty],
                    &[ty],
                    vec![
                        Node::new(
                            format!("IRInst.binop IRBinOp.{op} ({ty}) 0 1"),
                            &[99],
                            &[ty],
                        ),
                        Node::ret(&[99]),
                    ],
                )],
            );
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                17,
                &["IRScalar.int_ 13", "IRScalar.int_ 2"],
                "byte_machine_external_mem",
                29,
                2,
            );
            check(
                &mut spec,
                &format!("{ctx}_result"),
                "IROutcome",
                &outcome(&actual),
                &returned(&[&format!("IRScalar.int_ {expected}")]),
            );
        }
    });
}

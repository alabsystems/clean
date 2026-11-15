// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual byte-machine cast controls, not legacy cell-evaluator substitutions.
//! These checked model executions do not establish native/provider fidelity.

use super::{
    check, context, machine_spec, outcome, register, returned, run, world, Function, Node,
};
use crate::spec::Specification;

const LIVE: &str =
    "IRByteWorldV1.mk Nat byte_machine_external_mem 73 (IRList.cons Nat 1 (IRList.nil Nat)) 2";
const RETURNED: &str =
    "IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 byte_machine_external_mem) 73 (IRList.nil Nat) 2";
const BAD: &str = "IROutcome.type_error IRFault.bad_field";
const UNSUPPORTED: &str = "IROutcome.unmodelled IRFault.width_bounded";

fn cast(op: &str, src: &str, dst: &'static str, operand: u64, result: u64) -> Node {
    Node::new(
        format!("IRInst.cast IRCastOp.{op} ({src}) ({dst}) {operand}"),
        &[result],
        &[dst],
    )
}

fn success(
    spec: &mut Specification,
    name: &str,
    op: &str,
    src: &'static str,
    dst: &'static str,
    argument: &str,
    value: &str,
) {
    let ctx = format!("{name}_context");
    context(
        spec,
        &ctx,
        &[Function::local(
            41,
            &[src],
            &[dst],
            vec![cast(op, src, dst, 0, 77), Node::ret(&[77])],
        )],
    );
    let actual = run(
        &ctx,
        "byte_machine_no_import",
        41,
        &[argument],
        "byte_machine_external_mem",
        73,
        2,
    );
    check(
        spec,
        &format!("{name}_value"),
        "IROutcome",
        &outcome(&actual),
        &returned(&[value]),
    );
    check(
        spec,
        &format!("{name}_world"),
        "IRByteWorldV1 Nat",
        &world(&actual),
        RETURNED,
    );
}

fn refusal(
    spec: &mut Specification,
    name: &str,
    formal: &'static str,
    op: &str,
    src: &str,
    dst: &'static str,
    argument: &str,
    fault: &str,
) {
    let ctx = format!("{name}_context");
    // A separately typed formal gets through entry admission. An inconsistent
    // cast annotation therefore reaches the actual fetched cast's own checks.
    context(
        spec,
        &ctx,
        &[Function::local(
            41,
            &[formal],
            &[],
            vec![cast(op, src, dst, 0, 77), Node::ret(&[])],
        )],
    );
    let actual = run(
        &ctx,
        "byte_machine_no_import",
        41,
        &[argument],
        "byte_machine_external_mem",
        73,
        1,
    );
    check(
        spec,
        &format!("{name}_fault"),
        "IRByteConfigV1 Nat",
        &actual,
        &format!("IRByteConfigV1.halted Nat ({fault}) ({LIVE})"),
    );
}

#[test]
fn byte_cast_integer_and_bool_conversions_execute_existing_scalar_meanings() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (name, op, src, dst, argument, value) in [
            (
                "trunc_word",
                "trunc",
                "IRTy.uint_ 8",
                "IRTy.int_ 4",
                "IRScalar.int_ 255",
                "IRScalar.int_ 15",
            ),
            (
                "trunc_true",
                "trunc",
                "IRTy.int_ 8",
                "IRTy.bool_",
                "IRScalar.int_ 3",
                "IRScalar.bool_ Bool.true",
            ),
            (
                "trunc_false",
                "trunc",
                "IRTy.uint_ 8",
                "IRTy.bool_",
                "IRScalar.int_ 2",
                "IRScalar.bool_ Bool.false",
            ),
            (
                "zero_extend",
                "zext",
                "IRTy.int_ 4",
                "IRTy.uint_ 8",
                "IRScalar.int_ 15",
                "IRScalar.int_ 15",
            ),
            (
                "sign_extend",
                "sext",
                "IRTy.uint_ 4",
                "IRTy.int_ 8",
                "IRScalar.int_ 15",
                "IRScalar.int_ 255",
            ),
            (
                "zero_bool",
                "zext",
                "IRTy.bool_",
                "IRTy.uint_ 8",
                "IRScalar.bool_ Bool.true",
                "IRScalar.int_ 1",
            ),
            (
                "sign_bool",
                "sext",
                "IRTy.bool_",
                "IRTy.int_ 8",
                "IRScalar.bool_ Bool.true",
                "IRScalar.int_ 255",
            ),
            (
                "false_bool",
                "sext",
                "IRTy.bool_",
                "IRTy.uint_ 8",
                "IRScalar.bool_ Bool.false",
                "IRScalar.int_ 0",
            ),
            (
                "same_width",
                "bitcast",
                "IRTy.int_ 8",
                "IRTy.uint_ 8",
                "IRScalar.int_ 255",
                "IRScalar.int_ 255",
            ),
            (
                "equal_trunc",
                "trunc",
                "IRTy.uint_ 8",
                "IRTy.int_ 8",
                "IRScalar.int_ 129",
                "IRScalar.int_ 129",
            ),
            (
                "odd_width",
                "zext",
                "IRTy.uint_ 13",
                "IRTy.int_ 32",
                "IRScalar.int_ 8191",
                "IRScalar.int_ 8191",
            ),
            (
                "wide_width",
                "bitcast",
                "IRTy.int_ 128",
                "IRTy.uint_ 128",
                "IRScalar.int_ 340282366920938463463374607431768211455",
                "IRScalar.int_ 340282366920938463463374607431768211455",
            ),
        ] {
            success(
                &mut spec,
                &format!("byte_cast_{name}"),
                op,
                src,
                dst,
                argument,
                value,
            );
        }
    });
}

#[test]
fn byte_cast_pointer_roundtrip_preserves_zero_high_bit_and_maximum_words() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (index, (ty, word, pointer)) in [
            ("IRTy.int_ 64", "0", "IRScalar.nullptr_"),
            ("IRTy.uint_ 64", "16", "IRScalar.ptr_ 16"),
            (
                "IRTy.int_ 64",
                "9223372036854775808",
                "IRScalar.ptr_ 9223372036854775808",
            ),
            (
                "IRTy.uint_ 64",
                "18446744073709551615",
                "IRScalar.ptr_ 18446744073709551615",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = format!("byte_cast_roundtrip_context_{index}");
            context(
                &mut spec,
                &ctx,
                &[Function::local(
                    41,
                    &[ty],
                    &["IRTy.ptr_", ty],
                    vec![
                        cast("inttoptr", ty, "IRTy.ptr_", 0, 77),
                        cast("ptrtoint", "IRTy.ptr_", ty, 77, 99),
                        Node::ret(&[77, 99]),
                    ],
                )],
            );
            let argument = format!("IRScalar.int_ {word}");
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                41,
                &[&argument],
                "byte_machine_external_mem",
                73,
                3,
            );
            check(
                &mut spec,
                &format!("byte_cast_roundtrip_{index}"),
                "IROutcome",
                &outcome(&actual),
                &returned(&[pointer, &argument]),
            );
            check(
                &mut spec,
                &format!("byte_cast_roundtrip_world_{index}"),
                "IRByteWorldV1 Nat",
                &world(&actual),
                RETURNED,
            );
        }
    });
}

#[test]
fn byte_cast_thin_pointer_families_preserve_the_address_not_an_owner() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (index, ty) in [
            "IRTy.ptr_",
            "IRTy.ref_ (IRTy.int_ 8)",
            "IRTy.refmut_ (IRTy.int_ 8)",
            "IRTy.rawconst_ (IRTy.int_ 8)",
            "IRTy.rawmut_ (IRTy.int_ 8)",
            "IRTy.rc_ (IRTy.int_ 8)",
        ]
        .into_iter()
        .enumerate()
        {
            success(
                &mut spec,
                &format!("byte_cast_thin_make_{index}"),
                "inttoptr",
                "IRTy.int_ 64",
                ty,
                "IRScalar.int_ 8",
                "IRScalar.ptr_ 8",
            );
            success(
                &mut spec,
                &format!("byte_cast_thin_identity_{index}"),
                "ptrtoptr",
                ty,
                "IRTy.ptr_",
                "IRScalar.ptr_ 8",
                "IRScalar.ptr_ 8",
            );
            success(
                &mut spec,
                &format!("byte_cast_thin_null_{index}"),
                "ptrtoint",
                ty,
                "IRTy.uint_ 64",
                "IRScalar.nullptr_",
                "IRScalar.int_ 0",
            );
        }
    });
}

#[test]
fn byte_cast_step_binds_once_advances_once_and_preserves_the_exact_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        context(
            &mut spec,
            "byte_cast_step_context",
            &[Function::local(
                41,
                &["IRTy.int_ 64"],
                &["IRTy.ptr_"],
                vec![
                    cast("inttoptr", "IRTy.int_ 64", "IRTy.ptr_", 0, 77),
                    Node::ret(&[77]),
                ],
            )],
        );
        let initial = "ir_byte_init_v1 Nat byte_cast_step_context 41 (IRList.cons IRScalar (IRScalar.int_ 16) (IRList.nil IRScalar)) byte_machine_external_mem 73";
        let actual = format!(
            "ir_byte_step_v1 Nat byte_cast_step_context byte_machine_no_import ({initial})"
        );
        let expected = format!("IRByteConfigV1.running Nat (IRMachine.mk (IRList.cons IRFrame (IRFrame.mk 41 0 1 (IRList.cons IRBinding (IRBinding.mk 77 (IRScalar.ptr_ 16)) (IRList.cons IRBinding (IRBinding.mk 0 (IRScalar.int_ 16)) (IRList.nil IRBinding))) (IRList.nil Nat)) (IRList.nil IRFrame)) (IRList.nil IRMemSlot) 0) ({LIVE})");
        check(
            &mut spec,
            "byte_cast_exact_step",
            "IRByteConfigV1 Nat",
            &actual,
            &expected,
        );
    });
}

#[test]
fn byte_cast_malformed_carriers_are_rejected_at_the_fetched_cast() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (name, formal, op, src, dst, argument) in [
            (
                "bool_as_word",
                "IRTy.bool_",
                "inttoptr",
                "IRTy.int_ 64",
                "IRTy.ptr_",
                "IRScalar.bool_ Bool.true",
            ),
            (
                "word_as_pointer",
                "IRTy.int_ 64",
                "ptrtoint",
                "IRTy.ptr_",
                "IRTy.int_ 64",
                "IRScalar.int_ 16",
            ),
            (
                "pointer_as_word",
                "IRTy.ptr_",
                "inttoptr",
                "IRTy.uint_ 64",
                "IRTy.ptr_",
                "IRScalar.ptr_ 16",
            ),
            (
                "word_as_bool",
                "IRTy.uint_ 8",
                "zext",
                "IRTy.bool_",
                "IRTy.uint_ 64",
                "IRScalar.int_ 1",
            ),
            (
                "bool_as_integer",
                "IRTy.bool_",
                "trunc",
                "IRTy.uint_ 8",
                "IRTy.bool_",
                "IRScalar.bool_ Bool.true",
            ),
            (
                "narrow_noncanonical",
                "IRTy.uint_ 64",
                "zext",
                "IRTy.uint_ 8",
                "IRTy.uint_ 64",
                "IRScalar.int_ 256",
            ),
        ] {
            refusal(
                &mut spec,
                &format!("byte_cast_bad_{name}"),
                formal,
                op,
                src,
                dst,
                argument,
                BAD,
            );
        }
    });
}

#[test]
fn byte_cast_unsupported_types_widths_and_families_refuse_without_legacy_fallback() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (index, (op, src, dst)) in [
            ("inttoptr", "IRTy.int_ 32", "IRTy.ptr_"),
            ("inttoptr", "IRTy.uint_ 128", "IRTy.ptr_"),
            ("ptrtoint", "IRTy.ptr_", "IRTy.int_ 32"),
            ("ptrtoint", "IRTy.func_ 41", "IRTy.uint_ 64"),
            ("inttoptr", "IRTy.uint_ 64", "IRTy.func_ 41"),
            ("ptrtoptr", "IRTy.fatptr_ (IRTy.int_ 8)", "IRTy.ptr_"),
            ("trunc", "IRTy.uint_ 8", "IRTy.uint_ 16"),
            ("zext", "IRTy.int_ 16", "IRTy.int_ 8"),
            ("sext", "IRTy.int_ 16", "IRTy.int_ 8"),
            ("bitcast", "IRTy.int_ 8", "IRTy.uint_ 16"),
            ("bitcast", "IRTy.float_ 64", "IRTy.uint_ 64"),
            ("zext", "IRTy.uint_ 0", "IRTy.uint_ 64"),
            ("sext", "IRTy.uint_ 64", "IRTy.uint_ 129"),
            ("transmute", "IRTy.int_ 64", "IRTy.uint_ 64"),
            ("reifyfnpointer", "IRTy.func_ 41", "IRTy.func_ 41"),
            ("fptoui", "IRTy.float_ 64", "IRTy.uint_ 64"),
            ("sitofp", "IRTy.int_ 64", "IRTy.float_ 64"),
        ]
        .into_iter()
        .enumerate()
        {
            refusal(
                &mut spec,
                &format!("byte_cast_unsupported_{index}"),
                "IRTy.int_ 64",
                op,
                src,
                dst,
                "IRScalar.int_ 16",
                UNSUPPORTED,
            );
        }
        // Byte null/address semantics must not silently rewrite the older
        // cell model, which deliberately has no integer-to-pointer meaning.
        check(
            &mut spec,
            "byte_cast_legacy_inttoptr_unchanged",
            "IRStepResult",
            "ir_cast_eval IRCastOp.inttoptr (IRTy.int_ 64) IRTy.ptr_ (IRScalar.int_ 16)",
            "ir_width_fault",
        );
    });
}

#[test]
fn byte_cast_noncanonical_word_pointer_and_undefined_binding_fail_closed() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (index, (op, src, dst, value)) in [
            (
                "inttoptr",
                "IRTy.int_ 64",
                "IRTy.ptr_",
                "IRScalar.int_ 18446744073709551616",
            ),
            ("inttoptr", "IRTy.uint_ 64", "IRTy.ptr_", "IRScalar.undef_"),
            ("ptrtoint", "IRTy.ptr_", "IRTy.uint_ 64", "IRScalar.ptr_ 0"),
            (
                "ptrtoint",
                "IRTy.ptr_",
                "IRTy.int_ 64",
                "IRScalar.ptr_ 18446744073709551616",
            ),
            ("ptrtoptr", "IRTy.ptr_", "IRTy.ptr_", "IRScalar.fat_ 16 0"),
            ("ptrtoptr", "IRTy.ptr_", "IRTy.ptr_", "IRScalar.fnptr_ 41"),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = format!("byte_cast_untrusted_binding_context_{index}");
            context(
                &mut spec,
                &ctx,
                &[Function::local(
                    41,
                    &[src],
                    &[],
                    vec![cast(op, src, dst, 0, 77)],
                )],
            );
            // Deliberately malformed SSA values enter at step, not through
            // init's earlier value admission. The live world is still valid.
            let machine = format!("IRMachine.mk (IRList.cons IRFrame (IRFrame.mk 41 0 0 (IRList.cons IRBinding (IRBinding.mk 0 ({value})) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) (IRList.nil IRMemSlot) 0");
            let actual = format!("ir_byte_step_v1 Nat {ctx} byte_machine_no_import (IRByteConfigV1.running Nat ({machine}) ({LIVE}))");
            check(
                &mut spec,
                &format!("byte_cast_untrusted_binding_{index}"),
                "IRByteConfigV1 Nat",
                &actual,
                &format!("IRByteConfigV1.halted Nat ({BAD}) ({LIVE})"),
            );
        }
    });
}

#[test]
fn byte_cast_result_site_does_not_override_the_declared_destination() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (index, (results, types)) in [
            (vec![77], vec!["IRTy.int_ 64"]),
            (vec![], vec![]),
            (vec![77, 78], vec!["IRTy.ptr_", "IRTy.ptr_"]),
            (vec![77], vec!["IRTy.ptr_", "IRTy.ptr_"]),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = format!("byte_cast_bad_site_context_{index}");
            let mut node = cast("inttoptr", "IRTy.int_ 64", "IRTy.ptr_", 0, 77);
            node.results = results;
            node.types = types;
            context(
                &mut spec,
                &ctx,
                &[Function::local(41, &["IRTy.int_ 64"], &[], vec![node])],
            );
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                41,
                &["IRScalar.int_ 16"],
                "byte_machine_external_mem",
                73,
                1,
            );
            check(
                &mut spec,
                &format!("byte_cast_bad_site_{index}"),
                "IRByteConfigV1 Nat",
                &actual,
                &format!("IRByteConfigV1.halted Nat ({BAD}) ({LIVE})"),
            );
        }
    });
}

#[test]
fn byte_cast_pointer_creation_does_not_authorize_a_store() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (index, word) in ["0", "8", "32"].into_iter().enumerate() {
            let ctx = format!("byte_cast_unallocated_context_{index}");
            context(
                &mut spec,
                &ctx,
                &[Function::local(
                    41,
                    &["IRTy.int_ 64", "IRTy.int_ 64"],
                    &[],
                    vec![
                        cast("inttoptr", "IRTy.int_ 64", "IRTy.ptr_", 0, 77),
                        Node::new("IRInst.store (IRTy.int_ 64) 77 1 Bool.false", &[], &[]),
                        Node::ret(&[]),
                    ],
                )],
            );
            let argument = format!("IRScalar.int_ {word}");
            let actual = run(
                &ctx,
                "byte_machine_no_import",
                41,
                &[&argument, "IRScalar.int_ 41"],
                "byte_machine_external_mem",
                73,
                2,
            );
            check(
                &mut spec,
                &format!("byte_cast_unallocated_store_{index}"),
                "IRByteConfigV1 Nat",
                &actual,
                &format!("IRByteConfigV1.halted Nat (IROutcome.ub IRFault.bad_addr) ({LIVE})"),
            );
        }
    });
}

#[test]
fn byte_cast_checked_definitions_reject_a_fabricated_null_roundtrip_claim() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        context(
            &mut spec,
            "byte_cast_false_claim_context",
            &[Function::local(
                41,
                &["IRTy.int_ 64"],
                &["IRTy.ptr_"],
                vec![
                    cast("inttoptr", "IRTy.int_ 64", "IRTy.ptr_", 0, 77),
                    Node::ret(&[77]),
                ],
            )],
        );
        let actual = run(
            "byte_cast_false_claim_context",
            "byte_machine_no_import",
            41,
            &["IRScalar.int_ 0"],
            "byte_machine_external_mem",
            73,
            2,
        );
        let wrong = returned(&["IRScalar.ptr_ 0"]);
        // The valid execution is established first, so a missing declaration or
        // malformed fixture cannot turn this refusal into a false-positive.
        check(
            &mut spec,
            "byte_cast_null_control",
            "IROutcome",
            &outcome(&actual),
            &returned(&["IRScalar.nullptr_"]),
        );
        let error = spec.add_recursive_def(&format!("def byte_cast_forged_null : Eq IROutcome ({}) ({wrong}) := Eq.refl IROutcome ({wrong})", outcome(&actual)),
            "Deliberately false cast result, required to fail kernel checking.").expect_err("false null result must not be registered");
        crate::test_utils::assert_type_mismatch_rejection(&error, "byte_cast_forged_null");
        assert!(spec.get_definition("byte_cast_forged_null").is_none());
        // Ordinary registrations still work after the rejected definition.
        register(
            &mut spec,
            "def byte_cast_after_refusal : Eq Nat 7 7 := Eq.refl Nat 7",
        );
        spec.verify_definition("byte_cast_after_refusal")
            .expect("clean post-refusal replay");
    });
}

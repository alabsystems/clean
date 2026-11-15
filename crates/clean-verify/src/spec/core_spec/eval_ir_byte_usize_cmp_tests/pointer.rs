// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel-checked Byte-only address comparisons; no 32-bit machine-profile claim.

use super::*;

const OPS: [&str; 10] = [
    "eq_", "ne_", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
];

fn pointer(address: u128) -> String {
    if address == 0 {
        "IRScalar.nullptr_".into()
    } else {
        format!("IRScalar.ptr_ {address}")
    }
}

fn expected(op: &str, bits: u32, lhs: u128, rhs: u128) -> bool {
    let signed = |value: u128| {
        if value & (1u128 << (bits - 1)) == 0 {
            value as i128
        } else {
            value as i128 - (1i128 << bits)
        }
    };
    match op {
        "eq_" => lhs == rhs,
        "ne_" => lhs != rhs,
        "ult" => lhs < rhs,
        "ule" => lhs <= rhs,
        "ugt" => lhs > rhs,
        "uge" => lhs >= rhs,
        "slt" => signed(lhs) < signed(rhs),
        "sle" => signed(lhs) <= signed(rhs),
        "sgt" => signed(lhs) > signed(rhs),
        "sge" => signed(lhs) >= signed(rhs),
        _ => unreachable!(),
    }
}

#[test]
fn byte_pointer_icmp_all_predicates_are_exact_at_32_and_64_bits() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for root in [
            "ir_byte_pointer_comparison_address_at_v1",
            "ir_byte_pointer_icmp_at_v1",
            "ir_byte_icmp_eval_v1",
        ] {
            checked(&spec, root);
        }
        for bits in [32, 64] {
            let high = 1u128 << (bits - 1);
            let maximum = (1u128 << bits) - 1;
            for (index, (lhs, rhs)) in [
                (0, 0),
                (0, 16),
                (16, 0),
                (16, 16),
                (16, 24),
                (24, 16),
                (high, 0),
                (maximum, 16),
            ]
            .into_iter()
            .enumerate()
            {
                for op in OPS {
                    let actual = format!(
                        "ir_byte_pointer_icmp_at_v1 IRICmpOp.{op} {bits} ({}) ({})",
                        pointer(lhs),
                        pointer(rhs)
                    );
                    let answer = expected(op, bits, lhs, rhs);
                    let value = if answer { "Bool.true" } else { "Bool.false" };
                    let want = format!("IRStepResult.value (IRScalar.bool_ {value})");
                    check(
                        &mut spec,
                        &format!("ptr_cmp_{bits}_{index}_{op}"),
                        "IRStepResult",
                        &actual,
                        &want,
                    );
                    let wrong = if answer { "Bool.false" } else { "Bool.true" };
                    reject(
                        &mut spec,
                        &format!("ptr_cmp_wrong_{bits}_{index}_{op}"),
                        "IRStepResult",
                        &actual,
                        &format!("IRStepResult.value (IRScalar.bool_ {wrong})"),
                    );
                    if bits == 64 {
                        let dispatch = comparison(op, "IRTy.ptr_", &pointer(lhs), &pointer(rhs));
                        check(
                            &mut spec,
                            &format!("ptr_dispatch_{index}_{op}"),
                            "IRStepResult",
                            &dispatch,
                            &want,
                        );
                    }
                }
            }
        }
    });
}

#[test]
fn byte_pointer_icmp_preserves_poison_address_and_legacy_refusals() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for bits in [32, 64] {
            for op in OPS {
                for (index, (lhs, rhs, fault)) in [
                    (
                        "IRScalar.undef_".to_owned(),
                        pointer(16),
                        "ub IRFault.uninit",
                    ),
                    (
                        pointer(16),
                        "IRScalar.undef_".to_owned(),
                        "ub IRFault.uninit",
                    ),
                    (pointer(1u128 << bits), pointer(16), "ub IRFault.bad_addr"),
                    (pointer(16), pointer(1u128 << bits), "ub IRFault.bad_addr"),
                    (
                        "IRScalar.int_ 16".to_owned(),
                        pointer(16),
                        "type_error IRFault.not_ptr",
                    ),
                    (
                        pointer(16),
                        "IRScalar.bool_ Bool.true".to_owned(),
                        "type_error IRFault.not_ptr",
                    ),
                    (
                        pointer(1u128 << bits),
                        "IRScalar.undef_".to_owned(),
                        "ub IRFault.uninit",
                    ),
                ]
                .into_iter()
                .enumerate()
                {
                    let actual =
                        format!("ir_byte_pointer_icmp_at_v1 IRICmpOp.{op} {bits} ({lhs}) ({rhs})");
                    check(
                        &mut spec,
                        &format!("ptr_refusal_{bits}_{op}_{index}"),
                        "IRStepResult",
                        &actual,
                        &format!("IRStepResult.fault (IROutcome.{fault})"),
                    );
                }
            }
        }
        for bits in [0, 8, 16, 128] {
            check(
                &mut spec,
                &format!("ptr_width_refusal_{bits}"),
                "IRStepResult",
                &format!(
                    "ir_byte_pointer_icmp_at_v1 IRICmpOp.eq_ {bits} IRScalar.nullptr_ IRScalar.nullptr_"
                ),
                "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)",
            );
        }
        for op in ["ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"] {
            check(
                &mut spec,
                &format!("ptr_legacy_refusal_{op}"),
                "IRStepResult",
                &format!(
                    "ir_icmp_eval IRICmpOp.{op} IRTy.ptr_ IRScalar.nullptr_ (IRScalar.ptr_ 16)"
                ),
                "IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            );
        }
        check(
            &mut spec,
            "ptr_address_zero_alias",
            "IRStepResult",
            "ir_byte_pointer_icmp_at_v1 IRICmpOp.eq_ 64 (IRScalar.ptr_ 0) IRScalar.nullptr_",
            "IRStepResult.value (IRScalar.bool_ Bool.true)",
        );
        check(
            &mut spec,
            "ptr_legacy_zero_tag_distinct",
            "IRStepResult",
            "ir_icmp_eval IRICmpOp.eq_ IRTy.ptr_ (IRScalar.ptr_ 0) IRScalar.nullptr_",
            "IRStepResult.value (IRScalar.bool_ Bool.false)",
        );
    });
}

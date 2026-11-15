// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The admitted Bool/Usize64 cells of the actual Byte comparison dispatcher.

use super::*;

#[path = "scalar/fetched.rs"]
mod fetched;

const OPS: [&str; 10] = [
    "eq_", "ne_", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
];

fn expected(op: &str, bits: u32, lhs: u64, rhs: u64) -> bool {
    let signed = |value: u64| {
        if value & (1u64 << (bits - 1)) == 0 {
            i128::from(value)
        } else {
            i128::from(value) - (1i128 << bits)
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

fn boolean(value: bool) -> String {
    format!("IRScalar.bool_ Bool.{value}")
}

fn integer(value: u64) -> String {
    format!("IRScalar.int_ {value}")
}

fn result(value: bool) -> String {
    format!("IRStepResult.value ({})", boolean(value))
}

#[test]
fn byte_scalar_icmp_preserves_kinds_widths_poison_and_legacy_boundaries() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        checked(&spec, "ir_byte_bool_icmp_v1");
        checked(&spec, "ir_byte_icmp_eval_v1");
        for op in OPS {
            for (index, (left, right, error)) in [
                (
                    "IRScalar.undef_",
                    "IRScalar.bool_ Bool.false",
                    "ub IRFault.uninit",
                ),
                (
                    "IRScalar.bool_ Bool.true",
                    "IRScalar.undef_",
                    "ub IRFault.uninit",
                ),
                (
                    "IRScalar.int_ 0",
                    "IRScalar.bool_ Bool.false",
                    "type_error IRFault.not_bool",
                ),
                (
                    "IRScalar.bool_ Bool.false",
                    "IRScalar.ptr_ 16",
                    "type_error IRFault.not_bool",
                ),
                ("IRScalar.int_ 0", "IRScalar.undef_", "ub IRFault.uninit"),
            ]
            .into_iter()
            .enumerate()
            {
                check(
                    &mut spec,
                    &format!("scalar_bool_refusal_{op}_{index}"),
                    "IRStepResult",
                    &comparison(op, "IRTy.bool_", left, right),
                    &format!("IRStepResult.fault (IROutcome.{error})"),
                );
            }
            for bits in [0, 8, 32, 128] {
                check(
                    &mut spec,
                    &format!("scalar_usize_width_{op}_{bits}"),
                    "IRStepResult",
                    &comparison(op, &format!("IRTy.usize_ {bits}"), &integer(8), &integer(7)),
                    "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)",
                );
            }
            for (index, value) in [
                "IRScalar.bool_ Bool.true",
                "IRScalar.ptr_ 16",
                "IRScalar.undef_",
            ]
            .into_iter()
            .enumerate()
            {
                check(
                    &mut spec,
                    &format!("scalar_usize_kind_{op}_{index}"),
                    "IRStepResult",
                    &comparison(op, "IRTy.usize_ 64", value, &integer(7)),
                    "IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
                );
            }
            check(
                &mut spec,
                &format!("scalar_usize_legacy_{op}"),
                "IRStepResult",
                &format!(
                    "ir_icmp_eval IRICmpOp.{op} (IRTy.usize_ 64) (IRScalar.int_ 8) (IRScalar.int_ 7)"
                ),
                "IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            );
            if !matches!(op, "eq_" | "ne_") {
                check(
                    &mut spec,
                    &format!("scalar_bool_legacy_{op}"),
                    "IRStepResult",
                    &format!(
                        "ir_icmp_eval IRICmpOp.{op} IRTy.bool_ (IRScalar.bool_ Bool.true) (IRScalar.bool_ Bool.false)"
                    ),
                    "IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
                );
            }
        }
    });
}

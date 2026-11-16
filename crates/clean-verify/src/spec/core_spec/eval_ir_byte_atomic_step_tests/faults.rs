// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn byte_atomic_fetched_faults_retain_the_memory_at_the_actual_failure_point() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (index, pointer, increment, memory, fault) in [
            (
                0,
                "IRScalar.ptr_ 17",
                "IRScalar.int_ 1",
                MEMORY,
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                1,
                "IRScalar.ptr_ 48",
                "IRScalar.int_ 1",
                MEMORY,
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                2,
                "IRScalar.ptr_ 16",
                "IRScalar.bool_ Bool.true",
                MEMORY,
                "IROutcome.type_error IRFault.width_bounded",
            ),
            (
                3,
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 18446744073709551616",
                MEMORY,
                "IROutcome.type_error IRFault.width_bounded",
            ),
            (
                4,
                "IRScalar.ptr_ 24",
                "IRScalar.int_ 1",
                "(atomic_step_memory atomic_step_blank)",
                "IROutcome.ub IRFault.uninit",
            ),
            (
                5,
                "IRScalar.ptr_ 18446744073709551616",
                "IRScalar.int_ 1",
                MEMORY,
                "IROutcome.type_error IRFault.not_ptr",
            ),
            (
                6,
                "IRScalar.ptr_ 64",
                "IRScalar.int_ 1",
                MEMORY,
                "IROutcome.ub IRFault.bad_addr",
            ),
        ] {
            let frame = format!("(atomic_step_frame ({pointer}) ({increment}))");
            let actual = step("atomic_step_context", &frame, memory);
            let failed = format!("@IRByteConfigV1.halted Nat ({fault}) {}", world(memory));
            equality(
                &mut spec,
                &format!("atomic_step_fault_{index}"),
                CONFIG,
                &actual,
                &failed,
            );
        }
        for (name, types, site_pc, updated) in [
            ("site", RESULT_TYPES, 3, false),
            ("arity", "(@IRList.nil IRTy)", 2, false),
            (
                "result_type",
                "(@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))",
                2,
                true,
            ),
        ] {
            let actual = step(
                &context(INSTRUCTION, RESULTS, types, site_pc),
                BEFORE,
                MEMORY,
            );
            let fault = if name == "site" {
                "IROutcome.stuck IRFault.fetch_past_end"
            } else {
                "IROutcome.type_error IRFault.bad_field"
            };
            let final_memory = if updated { UPDATED } else { MEMORY };
            let failed = format!(
                "@IRByteConfigV1.halted Nat ({fault}) {}",
                world(final_memory)
            );
            equality(
                &mut spec,
                &format!("atomic_step_fault_{name}"),
                CONFIG,
                &actual,
                &failed,
            );
            if updated {
                let rollback = format!("@IRByteConfigV1.halted Nat ({fault}) {}", world(MEMORY));
                reject(
                    &mut spec,
                    "atomic_step_wrong_rollback",
                    &actual,
                    &rollback,
                    "atomic_step_fault_result_type providers bytes host",
                );
            }
        }
        let invalid_machine = format!(
            "IRMachine.mk (@IRList.cons IRFrame {BEFORE} atomic_step_tail)
  (@IRList.cons IRMemSlot (IRMemSlot.mk 200 (IRScalar.int_ 9) Bool.true) (@IRList.nil IRMemSlot)) 17"
        );
        let invalid = format!(
            "ir_byte_step_v1 Nat atomic_step_context providers
  (@IRByteConfigV1.running Nat ({invalid_machine}) {})",
            world(MEMORY)
        );
        equality(
            &mut spec,
            "atomic_step_legacy_memory_refused",
            CONFIG,
            &invalid,
            &format!(
                "@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_addr) {}",
                world(MEMORY)
            ),
        );
    });
}

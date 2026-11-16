// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn endpoint(frame: &str, old: u64, memory: &str) -> String {
    format!(
        "@IRByteConfigV1.running Nat
  (atomic_step_machine (ir_frame_advance (ir_frame_set_many {frame} {RESULTS}
    (@IRList.cons IRScalar (IRScalar.int_ {old}) (@IRList.nil IRScalar))))) {}",
        world(memory)
    )
}

#[test]
fn byte_atomic_live_pointer_substitution_changes_only_the_fetched_operand() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        // Both candidates are live, aligned and initialized in the SAME input
        // frame/world. The changed program chooses SSA56 rather than SSA40.
        let current = format!(
            "(ir_frame_set_many {BEFORE}
  (@IRList.cons Nat 56 (@IRList.nil Nat))
  (@IRList.cons IRScalar (IRScalar.ptr_ 32) (@IRList.nil IRScalar)))"
        );
        let baseline = step("atomic_step_context", &current, MEMORY);
        let baseline_result = endpoint(&current, 41, UPDATED);
        equality(
            &mut spec,
            "atomic_step_two_live_baseline",
            CONFIG,
            &baseline,
            &baseline_result,
        );
        let changed_ctx = context(
            "IRInst.atomic_fetch_add_relaxed_u64_seq 56 78",
            RESULTS,
            RESULT_TYPES,
            2,
        );
        let changed = step(&changed_ctx, &current, MEMORY);
        let changed_memory = "(IRByteMemoryV1.mk atomic_step_allocations
  (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 (atomic_step_memory bytes)) 32 8 78) 128)";
        let changed_result = endpoint(&current, 77, changed_memory);
        equality(
            &mut spec,
            "atomic_step_two_live_changed",
            CONFIG,
            &changed,
            &changed_result,
        );
        reject(
            &mut spec,
            "atomic_step_two_live_wrong_replay",
            &changed,
            &baseline_result,
            "atomic_step_two_live_baseline providers bytes host",
        );
        equality(
            &mut spec,
            "atomic_step_two_live_old",
            "IRScalar",
            &format!("atomic_step_result ({changed}) 99"),
            "IRScalar.int_ 77",
        );
        let memory = format!(
            "ir_byte_world_memory_v1 Nat
  (ir_byte_final_world_v1 Nat ({changed}))"
        );
        for (address, value) in [(16, 41), (32, 78)] {
            equality(
                &mut spec,
                &format!("atomic_step_two_live_read_{address}"),
                "IROption Nat",
                &format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({memory})) 8 {address}"),
                &format!("@IROption.some Nat {value}"),
            );
        }
    });
}

#[test]
fn byte_atomic_fetched_step_mutations_cannot_replay_the_original_endpoint() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let actual = step("atomic_step_context", BEFORE, MEMORY);
        let expected = expected();
        equality(
            &mut spec,
            "atomic_step_original",
            CONFIG,
            &actual,
            &expected,
        );
        for (name, instruction, results) in [
            (
                "pointer_id",
                "IRInst.atomic_fetch_add_relaxed_u64_seq 78 78",
                RESULTS,
            ),
            (
                "increment_id",
                "IRInst.atomic_fetch_add_relaxed_u64_seq 40 99",
                RESULTS,
            ),
            (
                "destination",
                INSTRUCTION,
                "(@IRList.cons Nat 100 (@IRList.nil Nat))",
            ),
        ] {
            let changed = step(
                &context(instruction, results, RESULT_TYPES, 2),
                BEFORE,
                MEMORY,
            );
            reject(
                &mut spec,
                &format!("atomic_step_changed_{name}"),
                &changed,
                &expected,
                "atomic_step_original providers bytes host",
            );
        }
        for (name, wrong) in [
            (
                "returns_new",
                expected.replace("IRScalar.int_ 41", "IRScalar.int_ 42"),
            ),
            ("stale_memory", expected.replace(UPDATED, MEMORY)),
            (
                "changed_host",
                expected.replace(
                    "host atomic_step_owners",
                    "(Nat.succ host) atomic_step_owners",
                ),
            ),
            (
                "changed_tail",
                expected.replace("atomic_step_machine", "atomic_step_machine_without_tail"),
            ),
        ] {
            if name == "changed_tail" {
                add(
                    &mut spec,
                    "atomic_step_machine_without_tail (frame : IRFrame)",
                    "IRMachine",
                    "IRMachine.mk (@IRList.cons IRFrame frame (@IRList.nil IRFrame)) (@IRList.nil IRMemSlot) 17",
                );
            }
            assert_ne!(wrong, expected);
            reject(
                &mut spec,
                &format!("atomic_step_wrong_{name}"),
                &actual,
                &wrong,
                "atomic_step_original providers bytes host",
            );
        }
    });
}

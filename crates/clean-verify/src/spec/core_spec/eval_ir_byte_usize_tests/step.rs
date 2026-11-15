// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const RESULTS: &str = "(IRList.cons Nat 99 (IRList.nil Nat))";
const TYPES: &str = "(IRList.cons IRTy (IRTy.usize_ 64) (IRList.nil IRTy))";
const INSTRUCTION: &str = "IRInst.atomic_fetch_add_relaxed_usize_seq 64 40 78";
const FRAME: &str = "(usize_frame (IRScalar.ptr_ 16))";
const CONFIG: &str = "IRByteConfigV1 Nat";
const UPDATED: &str = "IRByteMemoryV1.mk usize_allocs
  (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 (usize_memory 41)) 16 8 48) 128";

fn block(instruction: &str, results: &str) -> String {
    format!(
        "(IRBlock.mk 7 (IRList.nil Nat)
  (IRList.cons IRNode (IRNode.mk IRInst.unreachable (IRList.nil Nat))
    (IRList.cons IRNode (IRNode.mk IRInst.unreachable (IRList.nil Nat))
      (IRList.cons IRNode (IRNode.mk ({instruction}) {results}) (IRList.nil IRNode)))))"
    )
}

fn function(block: &str) -> String {
    format!(
        "(IRFunc.mk 9 (IRList.cons Nat 40 (IRList.cons Nat 78 (IRList.nil Nat))) 7
  (IRList.cons IRBlock {block} (IRList.nil IRBlock)))"
    )
}

fn context(instruction: &str, results: &str, types: &str, pc: u64) -> String {
    format!(
        "(IRByteContextV1.mk (IRModule.mk
  (IRList.cons IRFunc {} (IRList.nil IRFunc)) (IRList.nil IRGlobal))
  (IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.usize_ 64) 8 8
    (IRList.nil IRTy) (IRList.nil Nat)) (IRList.nil IRByteLayoutV1))
  (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1)
  (IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 {pc} 0 1 {types}) (IRList.nil IRByteSiteV1)))",
        function(&block(instruction, results))
    )
}

fn world(memory: &str) -> String {
    format!("(IRByteWorldV1.mk Nat ({memory}) 123 usize_owners 9)")
}

fn step(ctx: &str, frame: &str) -> String {
    format!(
        "ir_byte_step_v1 Nat ({ctx}) usize_providers
  (IRByteConfigV1.running Nat (usize_machine {frame}) {})",
        world("usize_memory 41")
    )
}

fn endpoint(frame: &str, old: u64, memory: &str) -> String {
    format!(
        "IRByteConfigV1.running Nat
  (usize_machine (ir_frame_advance (ir_frame_set_many {frame} {RESULTS}
    (IRList.cons IRScalar (IRScalar.int_ {old}) (IRList.nil IRScalar))))) {}",
        world(memory)
    )
}

fn fixture() -> Specification {
    let mut spec = super::fixture();
    for source in [
        r"def usize_owners : IRList Nat := IRList.cons Nat 7 (IRList.cons Nat 1 (IRList.nil Nat))",
        r"def usize_tail : IRList IRFrame := IRList.cons IRFrame
  (IRFrame.mk 3 4 5 (IRList.cons IRBinding (IRBinding.mk 777 (IRScalar.int_ 88)) (IRList.nil IRBinding))
    (IRList.cons Nat 55 (IRList.nil Nat))) (IRList.nil IRFrame)",
        r"def usize_frame (pointer : IRScalar) : IRFrame := IRFrame.mk 9 7 2
  (IRList.cons IRBinding (IRBinding.mk 40 pointer)
    (IRList.cons IRBinding (IRBinding.mk 78 (IRScalar.int_ 7))
      (IRList.cons IRBinding (IRBinding.mk 56 (IRScalar.ptr_ 32))
        (IRList.cons IRBinding (IRBinding.mk 99 (IRScalar.int_ 777)) (IRList.nil IRBinding)))))
  (IRList.cons Nat 123 (IRList.nil Nat))",
        r"def usize_machine (frame : IRFrame) : IRMachine := IRMachine.mk
  (IRList.cons IRFrame frame usize_tail) (IRList.nil IRMemSlot) 17",
        r"def usize_providers : IRByteProvidersV1 Nat :=
fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) =>
  IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) mem host",
    ] {
        register(&mut spec, source);
    }
    register(
        &mut spec,
        &format!(
            "def usize_step_ctx : IRByteContextV1 := {}",
            context(INSTRUCTION, RESULTS, TYPES, 2)
        ),
    );
    spec
}

#[test]
fn byte_usize_fetched_step_derives_the_entire_world_from_inhabited_representation() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let actual = step("usize_step_ctx", FRAME);
        let expected = endpoint(FRAME, 41, UPDATED);
        check(&mut spec, "usize_fetched_exact", CONFIG, &actual, &expected);
        let block = block(INSTRUCTION, RESULTS);
        let function = function(&block);
        let args = format!("Nat usize_step_ctx usize_providers {FRAME} usize_tail
  (IRList.nil IRMemSlot) 17 (usize_memory 41) 123 usize_owners 9
  40 78 99 0 1 {function} {block} 16 41 7
  (Nat.le_add_right 17 18446744073709551599)
  (Eq.refl (IROption IRByteLayoutV1) (IROption.some IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.usize_ 64) 8 8 (IRList.nil IRTy) (IRList.nil Nat))))
  (Eq.refl Bool Bool.true)
  (ir_byte_usize64_rep_write_v1 (IRByteMemoryV1.mk usize_allocs (ir_byte_write_word_v1 usize_blank 32 8 77) 128) 16 41)
  (Nat.le_add_right 49 18446744073709551567)
  (Eq.refl Bool Bool.true)
  (Eq.refl IRScalar (IRScalar.ptr_ 16)) (Eq.refl IRScalar (IRScalar.int_ 7))
  (Eq.refl (IROption IRFunc) (IROption.some IRFunc {function}))
  (Eq.refl (IROption IRBlock) (IROption.some IRBlock {block}))
  (Eq.refl (IROption IRNode) (IROption.some IRNode (IRNode.mk ({INSTRUCTION}) {RESULTS})))
  (Eq.refl (IROption IRByteSiteV1) (IROption.some IRByteSiteV1 (IRByteSiteV1.mk 9 7 2 0 1 {TYPES})))");
        register(&mut spec, &format!("def usize_fetched_by_law : Eq ({CONFIG}) ({actual}) ({expected}) := ir_byte_step_fetch_add_relaxed_usize64_seq_below_v1 {args}"));
        checked(&spec, "usize_fetched_by_law");
        for (suffix, base, expected, extra) in [
            ("new", 16, 48, ""),
            ("frame", 32, 77, "32 8 (@Or.inr (Nat.le (Nat.add 32 8) 16) (Nat.le (Nat.add 16 8) 32) (Nat.le_add_right 24 8))"),
        ] {
            register(&mut spec, &format!("def usize_fetched_{suffix}_by_law : Eq (IROption Nat)
  (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_world_memory_v1 Nat (ir_byte_final_world_v1 Nat ({actual})))) 8 {base})
  (IROption.some Nat {expected}) := ir_byte_step_fetch_add_relaxed_usize64_seq_{suffix}_v1 {args} {extra}"));
            checked(&spec, &format!("usize_fetched_{suffix}_by_law"));
        }
    });
}

#[test]
fn byte_usize_fetched_operand_endpoint_and_site_mutations_are_observable() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let original = step("usize_step_ctx", FRAME);
        let expected = endpoint(FRAME, 41, UPDATED);
        for (name, inst, results, pc) in [
            (
                "width",
                "IRInst.atomic_fetch_add_relaxed_usize_seq 32 40 78",
                RESULTS,
                2,
            ),
            (
                "live_pointer",
                "IRInst.atomic_fetch_add_relaxed_usize_seq 64 56 78",
                RESULTS,
                2,
            ),
            (
                "increment",
                "IRInst.atomic_fetch_add_relaxed_usize_seq 64 40 99",
                RESULTS,
                2,
            ),
            (
                "destination",
                INSTRUCTION,
                "(IRList.cons Nat 100 (IRList.nil Nat))",
                2,
            ),
            ("site", INSTRUCTION, RESULTS, 3),
        ] {
            reject(
                &mut spec,
                &format!("usize_changed_{name}"),
                CONFIG,
                &step(&context(inst, results, TYPES, pc), FRAME),
                &expected,
            );
        }
        // Both pointers are live/initialized. The changed program has its own
        // real successful endpoint, not a fault used as a substitute control.
        let live = step(
            &context(
                "IRInst.atomic_fetch_add_relaxed_usize_seq 64 56 78",
                RESULTS,
                TYPES,
                2,
            ),
            FRAME,
        );
        let changed_mem = "IRByteMemoryV1.mk usize_allocs (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 (usize_memory 41)) 32 8 84) 128";
        check(
            &mut spec,
            "usize_other_live_endpoint",
            CONFIG,
            &live,
            &endpoint(FRAME, 77, changed_mem),
        );
        // The fetched site checks declared arity before execution. A matching
        // site can still fail at the actual result bind AFTER the RMW; preserve
        // the memory at that precise failure point, not a generic rollback.
        for (name, results, types, memory) in [
            (
                "wrong_result_type",
                RESULTS,
                "(IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy))",
                UPDATED,
            ),
            (
                "missing_result_at_site",
                "(IRList.nil Nat)",
                TYPES,
                "usize_memory 41",
            ),
            (
                "missing_result_at_bind",
                "(IRList.nil Nat)",
                "(IRList.nil IRTy)",
                UPDATED,
            ),
        ] {
            let actual = step(&context(INSTRUCTION, results, types, 2), FRAME);
            check(
                &mut spec,
                &format!("usize_{name}_exact_fault_world"),
                CONFIG,
                &actual,
                &format!(
                    "IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {}",
                    world(memory)
                ),
            );
            let wrong_memory = if memory == UPDATED {
                "usize_memory 41"
            } else {
                UPDATED
            };
            reject(
                &mut spec,
                &format!("usize_{name}_wrong_fault_world"),
                CONFIG,
                &actual,
                &format!(
                    "IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {}",
                    world(wrong_memory)
                ),
            );
        }
        for (name, wrong) in [
            ("new_as_old", endpoint(FRAME, 48, UPDATED)),
            ("stale", endpoint(FRAME, 41, "usize_memory 41")),
            (
                "host",
                expected.replace("123 usize_owners", "124 usize_owners"),
            ),
            ("cursor", expected.replace(") 128)", ") 129)")),
            (
                "pc",
                expected.replace("ir_frame_advance", "ir_frame_advance_twice"),
            ),
        ] {
            if name == "pc" {
                register(&mut spec, "def ir_frame_advance_twice (f : IRFrame) : IRFrame := ir_frame_advance (ir_frame_advance f)");
            }
            assert_ne!(wrong, expected, "mutation must change its endpoint");
            reject(
                &mut spec,
                &format!("usize_wrong_{name}"),
                CONFIG,
                &original,
                &wrong,
            );
        }
    });
}

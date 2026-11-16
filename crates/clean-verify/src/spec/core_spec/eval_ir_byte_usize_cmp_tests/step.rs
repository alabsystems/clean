// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const CONFIG: &str = "IRByteConfigV1 Nat";
const RESULTS: &str = "(@IRList.cons Nat 99 (@IRList.nil Nat))";
const TYPES: &str = "(@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))";
const INSTRUCTION: &str = "IRInst.icmp IRICmpOp.ugt (IRTy.usize_ 64) 40 78";

fn block(inst: &str, results: &str) -> String {
    format!(
        "(IRBlock.mk 7 (@IRList.nil Nat)
  (@IRList.cons IRNode (IRNode.mk IRInst.unreachable (@IRList.nil Nat))
    (@IRList.cons IRNode (IRNode.mk IRInst.unreachable (@IRList.nil Nat))
      (@IRList.cons IRNode (IRNode.mk ({inst}) {results}) (@IRList.nil IRNode)))))"
    )
}

fn function(block: &str) -> String {
    format!(
        "(IRFunc.mk 9 (@IRList.cons Nat 40 (@IRList.cons Nat 78 (@IRList.nil Nat))) 7
  (@IRList.cons IRBlock {block} (@IRList.nil IRBlock)))"
    )
}

fn context(inst: &str, results: &str, types: &str, pc: u64) -> String {
    format!(
        "(IRByteContextV1.mk (IRModule.mk
  (@IRList.cons IRFunc {} (@IRList.nil IRFunc)) (@IRList.nil IRGlobal))
  (@IRList.nil IRByteLayoutV1) (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1)
  (@IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 {pc} 0 1 {types}) (@IRList.nil IRByteSiteV1)))",
        function(&block(inst, results))
    )
}

fn frame(old: u64) -> String {
    format!("(cmp_frame (IRScalar.int_ {old}))")
}

fn actual(ctx: &str, frame: &str) -> String {
    format!(
        "ir_byte_step_v1 Nat ({ctx}) cmp_providers
  (@IRByteConfigV1.running Nat (cmp_machine {frame}) cmp_world)"
    )
}

fn expected(frame: &str, value: bool) -> String {
    format!(
        "@IRByteConfigV1.running Nat (cmp_machine
  (ir_frame_advance (ir_frame_set_many {frame} {RESULTS}
    (@IRList.cons IRScalar (IRScalar.bool_ Bool.{value}) (@IRList.nil IRScalar))))) cmp_world"
    )
}

fn fixture() -> Specification {
    let mut spec = super::fixture();
    for source in [
        "def cmp_owners : IRList Nat := @IRList.cons Nat 7 (@IRList.cons Nat 1 (@IRList.nil Nat))".to_owned(),
        r"def cmp_tail : IRList IRFrame := @IRList.cons IRFrame
  (IRFrame.mk 3 4 5 (@IRList.cons IRBinding (IRBinding.mk 777 (IRScalar.int_ 88)) (@IRList.nil IRBinding))
    (@IRList.cons Nat 55 (@IRList.nil Nat))) (@IRList.nil IRFrame)".to_owned(),
        format!("def cmp_frame (old : IRScalar) : IRFrame := IRFrame.mk 9 7 2
  (@IRList.cons IRBinding (IRBinding.mk 40 old)
    (@IRList.cons IRBinding (IRBinding.mk 78 (IRScalar.int_ {MAX}))
      (@IRList.cons IRBinding (IRBinding.mk 56 (IRScalar.int_ {}))
        (@IRList.cons IRBinding (IRBinding.mk 57 (IRScalar.int_ 0))
          (@IRList.cons IRBinding (IRBinding.mk 99 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding))))))
  (@IRList.cons Nat 123 (@IRList.nil Nat))", MAX + 1),
        r"def cmp_machine (frame : IRFrame) : IRMachine := IRMachine.mk
  (@IRList.cons IRFrame frame cmp_tail) (@IRList.nil IRMemSlot) 17".to_owned(),
        r"def cmp_memory : IRByteMemoryV1 := IRByteMemoryV1.mk
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 32 7 Bool.true) (@IRList.nil IRByteAllocationV1))
  (ir_byte_write_word_v1 (fun (_ : Nat) => @IROption.none Nat) 16 8 41) 128".to_owned(),
        "def cmp_world : IRByteWorldV1 Nat := @IRByteWorldV1.mk Nat cmp_memory 123 cmp_owners 9".to_owned(),
        r"def cmp_providers : IRByteProvidersV1 Nat :=
fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) =>
  @IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) mem host".to_owned(),
        format!("def cmp_context : IRByteContextV1 := {}", context(INSTRUCTION, RESULTS, TYPES, 2)),
    ] { register(&mut spec, &source); }
    spec
}

fn arguments(old: u64) -> String {
    let block = block(INSTRUCTION, RESULTS);
    let function = function(&block);
    format!("Nat cmp_context cmp_providers {} cmp_tail (@IRList.nil IRMemSlot) 17 cmp_world
  40 78 99 0 1 {function} {block} {old} {MAX}
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl IRScalar (IRScalar.int_ {old})) (@Eq.refl IRScalar (IRScalar.int_ {MAX}))
  (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc {function}))
  (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock {block}))
  (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk ({INSTRUCTION}) {RESULTS})))
  (@Eq.refl (IROption IRByteSiteV1) (@IROption.some IRByteSiteV1 (IRByteSiteV1.mk 9 7 2 0 1 {TYPES})))", frame(old))
}

#[test]
fn byte_usize_cmp_fetched_boundary_laws_are_inhabited_and_preserve_exact_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (suffix, old, result) in [
            ("below", MAX - 1, false),
            ("equal", MAX, false),
            ("above", MAX + 1, true),
        ] {
            let frame = frame(old);
            let actual = actual("cmp_context", &frame);
            let expected = expected(&frame, result);
            check(
                &mut spec,
                &format!("cmp_step_{suffix}_compute"),
                CONFIG,
                &actual,
                &expected,
            );
            let args = arguments(old);
            for (name, ty, lhs, rhs, application) in [
                ("step", CONFIG, actual.clone(), expected.clone(), format!("ir_byte_step_icmp_usize64_ugt_v1 {args}")),
                ("run", CONFIG, format!("ir_byte_run_v1 Nat cmp_context cmp_providers 1 (@IRByteConfigV1.running Nat (cmp_machine {frame}) cmp_world)"), expected.clone(), format!("ir_byte_run_icmp_usize64_ugt_one_v1 {args}")),
                ("world", "IRByteWorldV1 Nat", format!("ir_byte_final_world_v1 Nat ({actual})"), "cmp_world".to_owned(), format!("ir_byte_step_icmp_usize64_ugt_world_v1 {args}")),
            ] {
                let name = format!("cmp_{suffix}_{name}_law");
                register(&mut spec, &format!("def {name} : @Eq ({ty}) ({lhs}) ({rhs}) := {application}"));
                checked(&spec, &name);
            }
        }
    });
}

#[test]
fn byte_usize_cmp_fetched_mutations_and_malformed_operands_are_observable() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let frame = frame(MAX);
        let correct = expected(&frame, false);
        for (suffix, inst, results, types, pc) in [
            (
                "left_ssa",
                "IRInst.icmp IRICmpOp.ugt (IRTy.usize_ 64) 56 78",
                RESULTS,
                TYPES,
                2,
            ),
            (
                "right_ssa",
                "IRInst.icmp IRICmpOp.ugt (IRTy.usize_ 64) 40 57",
                RESULTS,
                TYPES,
                2,
            ),
            (
                "comparison",
                "IRInst.icmp IRICmpOp.uge (IRTy.usize_ 64) 40 78",
                RESULTS,
                TYPES,
                2,
            ),
            (
                "width",
                "IRInst.icmp IRICmpOp.ugt (IRTy.usize_ 32) 40 78",
                RESULTS,
                TYPES,
                2,
            ),
            (
                "destination",
                INSTRUCTION,
                "(@IRList.cons Nat 100 (@IRList.nil Nat))",
                TYPES,
                2,
            ),
            (
                "result_type",
                INSTRUCTION,
                RESULTS,
                "(@IRList.cons IRTy (IRTy.usize_ 64) (@IRList.nil IRTy))",
                2,
            ),
            ("site", INSTRUCTION, RESULTS, TYPES, 3),
        ] {
            reject(
                &mut spec,
                &format!("cmp_mutant_{suffix}"),
                CONFIG,
                &actual(&context(inst, results, types, pc), &frame),
                &correct,
            );
        }
        // A different LIVE canonical SSA operand has its own success result;
        // the mutation is not detected only because it faults.
        check(
            &mut spec,
            "cmp_changed_operand_is_live",
            CONFIG,
            &actual(
                &context(
                    "IRInst.icmp IRICmpOp.ugt (IRTy.usize_ 64) 56 78",
                    RESULTS,
                    TYPES,
                    2,
                ),
                &frame,
            ),
            &expected(&frame, true),
        );
        let actual = actual("cmp_context", &frame);
        for (name, wrong) in [
            ("bool", expected(&frame, true)),
            ("pc", correct.replace("ir_frame_advance", "ir_frame_advance_bad")),
            ("host", correct.replace("cmp_world", "(@IRByteWorldV1.mk Nat cmp_memory 124 cmp_owners 9)")),
            ("memory", correct.replace("cmp_world", "(@IRByteWorldV1.mk Nat (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 cmp_memory) (fun (_ : Nat) => @IROption.none Nat) 128) 123 cmp_owners 9)")),
            ("cursor", correct.replace("cmp_machine", "cmp_machine_bad")),
        ] {
            if name == "pc" { register(&mut spec, "def ir_frame_advance_bad (frame : IRFrame) : IRFrame := frame"); }
            if name == "cursor" { register(&mut spec, "def cmp_machine_bad (frame : IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame frame cmp_tail) (@IRList.nil IRMemSlot) 18"); }
            reject(&mut spec, &format!("cmp_wrong_{name}"), CONFIG, &actual, &wrong);
        }
        for (name, value) in [
            ("pointer", "IRScalar.ptr_ 16"),
            ("noncanonical", "IRScalar.int_ 18446744073709551616"),
        ] {
            check(
                &mut spec,
                &format!("cmp_fault_{name}"),
                CONFIG,
                &self::actual("cmp_context", &format!("(cmp_frame ({value}))")),
                "@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) cmp_world",
            );
            let bad_right = format!(
                "(ir_frame_set_many {frame}
  (@IRList.cons Nat 78 (@IRList.nil Nat))
  (@IRList.cons IRScalar ({value}) (@IRList.nil IRScalar)))"
            );
            check(
                &mut spec,
                &format!("cmp_fault_right_{name}"),
                CONFIG,
                &self::actual("cmp_context", &bad_right),
                "@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) cmp_world",
            );
        }
    });
}

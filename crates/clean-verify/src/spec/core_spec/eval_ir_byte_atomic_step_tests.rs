// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fetched sequential-instruction controls over the actual ByteV1 dispatcher.
//! These authored module fixtures do not establish compiler reflection,
//! pointer ownership, concurrent atomicity, or an Arc implementation theorem.

use crate::spec::Specification;
use clean_kernel::Name;

#[path = "eval_ir_byte_atomic_step_tests/faults.rs"]
mod faults;

#[path = "eval_ir_byte_atomic_step_tests/mutations.rs"]
mod mutations;

const CONFIG: &str = "IRByteConfigV1 Nat";
const PARAMS: &str = "(providers : IRByteProvidersV1 Nat)
  (bytes : Nat -> IROption Nat) (host : Nat)";
const RESULTS: &str = "(@IRList.cons Nat 99 (@IRList.nil Nat))";
const RESULT_TYPES: &str = "(@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))";
const INSTRUCTION: &str = "IRInst.atomic_fetch_add_relaxed_u64_seq 40 78";
const BEFORE: &str = "(atomic_step_frame (IRScalar.ptr_ 16) (IRScalar.int_ 1))";
const MEMORY: &str = "(atomic_step_memory bytes)";
const UPDATED: &str = "(IRByteMemoryV1.mk atomic_step_allocations
  (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 (atomic_step_memory bytes)) 16 8 42) 128)";

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("installed definition");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("kernel-checked definition");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, name: &str, ty: &str, value: &str) {
    spec.add_recursive_def(
        &format!("def {name} : {ty} := {value}"),
        "Fetched sequential fetch-add test fixture",
    )
    .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(
        spec,
        name.split_whitespace().next().expect("declaration name"),
    );
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!("{name} {PARAMS}"),
        &format!("@Eq ({ty}) ({actual}) ({expected})"),
        &format!("@Eq.refl ({ty}) ({expected})"),
    );
}

fn reject(spec: &mut Specification, name: &str, actual: &str, wrong: &str, proof: &str) {
    let source = format!("def {name} {PARAMS} : @Eq ({CONFIG}) ({actual}) ({wrong}) := {proof}");
    let error = spec
        .add_recursive_def(&source, "Deliberately false fetched fetch-add endpoint")
        .expect_err("incorrect execution endpoint must fail");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn block(instruction: &str, results: &str) -> String {
    format!(
        "(IRBlock.mk 7 (@IRList.nil Nat)
        (@IRList.cons IRNode (IRNode.mk IRInst.unreachable (@IRList.nil Nat))
          (@IRList.cons IRNode (IRNode.mk IRInst.unreachable (@IRList.nil Nat))
            (@IRList.cons IRNode (IRNode.mk ({instruction}) {results}) (@IRList.nil IRNode)))))"
    )
}

fn function(block: &str) -> String {
    format!(
        "(IRFunc.mk 9 (@IRList.cons Nat 40 (@IRList.cons Nat 78 (@IRList.nil Nat))) 7
      (@IRList.cons IRBlock {block} (@IRList.nil IRBlock)))"
    )
}

fn context(instruction: &str, results: &str, types: &str, site_pc: u64) -> String {
    let function = function(&block(instruction, results));
    format!(
        "(IRByteContextV1.mk
  (IRModule.mk (@IRList.cons IRFunc {function} (@IRList.nil IRFunc)) (@IRList.nil IRGlobal))
  (@IRList.cons IRByteLayoutV1
    (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))
    (@IRList.nil IRByteLayoutV1))
  (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1)
  (@IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 {site_pc} 0 1 {types})
    (@IRList.nil IRByteSiteV1)))"
    )
}

fn world(memory: &str) -> String {
    format!("(@IRByteWorldV1.mk Nat {memory} host atomic_step_owners 5)")
}

fn step(ctx: &str, frame: &str, memory: &str) -> String {
    format!(
        "ir_byte_step_v1 Nat {ctx} providers
  (@IRByteConfigV1.running Nat (atomic_step_machine {frame}) {})",
        world(memory)
    )
}

fn expected() -> String {
    format!(
        "@IRByteConfigV1.running Nat
  (atomic_step_machine (ir_frame_advance (ir_frame_set_many {BEFORE} {RESULTS}
    (@IRList.cons IRScalar (IRScalar.int_ 41) (@IRList.nil IRScalar))))) {}",
        world(UPDATED)
    )
}

fn fixture() -> Specification {
    let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("shared public ByteV1 vocabulary");
    for (name, ty, value) in [
        (
            "atomic_step_allocations",
            "IRList IRByteAllocationV1",
            "@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 32 2 Bool.true)
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 3 Bool.false)
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 80 8 0 Bool.true)
      (@IRList.nil IRByteAllocationV1)))",
        ),
        ("atomic_step_owners", "IRList Nat", "@IRList.cons Nat 2 (@IRList.cons Nat 1 (@IRList.nil Nat))"),
        (
            "atomic_step_tail",
            "IRList IRFrame",
            "@IRList.cons IRFrame (IRFrame.mk 3 4 5
  (@IRList.cons IRBinding (IRBinding.mk 777 (IRScalar.int_ 88)) (@IRList.nil IRBinding))
  (@IRList.cons Nat 55 (@IRList.nil Nat))) (@IRList.nil IRFrame)",
        ),
        (
            "atomic_step_frame (pointer increment : IRScalar)",
            "IRFrame",
            "IRFrame.mk 9 7 2
  (@IRList.cons IRBinding (IRBinding.mk 40 pointer)
    (@IRList.cons IRBinding (IRBinding.mk 78 increment)
      (@IRList.cons IRBinding (IRBinding.mk 99 (IRScalar.int_ 777))
        (@IRList.cons IRBinding (IRBinding.mk 55 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)))))
  (@IRList.cons Nat 123 (@IRList.nil Nat))",
        ),
        (
            "atomic_step_machine (frame : IRFrame)",
            "IRMachine",
            "IRMachine.mk (@IRList.cons IRFrame frame atomic_step_tail) (@IRList.nil IRMemSlot) 17",
        ),
        (
            "atomic_step_memory (bytes : Nat -> IROption Nat)",
            "IRByteMemoryV1",
            "IRByteMemoryV1.mk atomic_step_allocations
  (ir_byte_write_word_v1 (ir_byte_write_word_v1 bytes 32 8 77) 16 8 41) 128",
        ),
        ("atomic_step_blank", "Nat -> IROption Nat", "fun (_ : Nat) => @IROption.none Nat"),
        (
            "atomic_step_result (c : IRByteConfigV1 Nat) (id : Nat)",
            "IRScalar",
            "match c with
| IRByteConfigV1.running machine world => ir_getd machine id
| IRByteConfigV1.halted outcome world => IRScalar.undef_",
        ),
        (
            "atomic_step_pc (c : IRByteConfigV1 Nat)",
            "Nat",
            "match c with
| IRByteConfigV1.running machine world =>
  match ir_mach_frames machine with
  | IRList.nil => 0
  | IRList.cons frame tail => ir_frame_pc frame
| IRByteConfigV1.halted outcome world => 0",
        ),
    ] {
        add(&mut spec, name, ty, value);
    }
    add(
        &mut spec,
        "atomic_step_context",
        "IRByteContextV1",
        &context(INSTRUCTION, RESULTS, RESULT_TYPES, 2),
    );
    spec
}

#[test]
fn byte_atomic_fetched_step_binds_old_result_and_preserves_exact_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for root in [
            "ir_byte_step_fetch_add_relaxed_u64_seq_below_v1",
            "ir_byte_run_fetch_add_relaxed_u64_seq_one_v1",
            "ir_byte_step_fetch_add_relaxed_u64_seq_world_v1",
            "ir_byte_step_fetch_add_relaxed_u64_seq_new_v1",
            "ir_byte_step_fetch_add_relaxed_u64_seq_frame_v1",
        ] {
            checked(&spec, root);
        }
        let actual = step("atomic_step_context", BEFORE, MEMORY);
        equality(&mut spec, "atomic_step_exact", CONFIG, &actual, &expected());
        let final_world = format!("ir_byte_final_world_v1 Nat ({actual})");
        let memory = format!("ir_byte_world_memory_v1 Nat ({final_world})");
        for (name, ty, observed, expected) in [
            (
                "old",
                "IRScalar",
                format!("atomic_step_result ({actual}) 99"),
                "IRScalar.int_ 41",
            ),
            (
                "preserved_local",
                "IRScalar",
                format!("atomic_step_result ({actual}) 55"),
                "IRScalar.bool_ Bool.true",
            ),
            (
                "advanced_once",
                "Nat",
                format!("atomic_step_pc ({actual})"),
                "3",
            ),
            (
                "updated",
                "IROption Nat",
                format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({memory})) 8 16"),
                "@IROption.some Nat 42",
            ),
            (
                "frame",
                "IROption Nat",
                format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({memory})) 8 32"),
                "@IROption.some Nat 77",
            ),
            (
                "allocations",
                "IRList IRByteAllocationV1",
                format!("ir_byte_mem_allocs_v1 ({memory})"),
                "atomic_step_allocations",
            ),
            (
                "cursor",
                "Nat",
                format!("ir_byte_mem_next_v1 ({memory})"),
                "128",
            ),
            (
                "host",
                "Nat",
                format!("ir_byte_world_host_v1 Nat ({final_world})"),
                "host",
            ),
            (
                "owners",
                "IRList Nat",
                format!("ir_byte_world_owners_v1 Nat ({final_world})"),
                "atomic_step_owners",
            ),
            (
                "next_owner",
                "Nat",
                format!("ir_byte_world_next_v1 Nat ({final_world})"),
                "5",
            ),
        ] {
            equality(
                &mut spec,
                &format!("atomic_step_observe_{name}"),
                ty,
                &observed,
                expected,
            );
        }
    });
}

#[test]
fn byte_atomic_fetched_theorem_has_inhabited_representation_and_lookup_premises() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let block = block(INSTRUCTION, RESULTS);
        let function = function(&block);
        let node = format!("(IRNode.mk ({INSTRUCTION}) {RESULTS})");
        let site = format!("(IRByteSiteV1.mk 9 7 2 0 1 {RESULT_TYPES})");
        let args = format!(
            "Nat atomic_step_context providers {BEFORE} atomic_step_tail
  (@IRList.nil IRMemSlot) 17 {MEMORY} host atomic_step_owners 5
  40 78 99 0 1 {function} {block} 16 41 1
  (Nat.le_add_right 17 18446744073709551599)
  (@Eq.refl (IROption IRByteLayoutV1)
    (@IROption.some IRByteLayoutV1
      (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))))
  (@Eq.refl Bool Bool.true)
  (ir_byte_u64_rep_write_v1
    (IRByteMemoryV1.mk atomic_step_allocations (ir_byte_write_word_v1 bytes 32 8 77) 128) 16 41)
  (Nat.le_add_right 43 18446744073709551573)
  (@Eq.refl Bool Bool.true)
  (@Eq.refl IRScalar (IRScalar.ptr_ 16))
  (@Eq.refl IRScalar (IRScalar.int_ 1))
  (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc {function}))
  (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock {block}))
  (@Eq.refl (IROption IRNode) (@IROption.some IRNode {node}))
  (@Eq.refl (IROption IRByteSiteV1) (@IROption.some IRByteSiteV1 {site}))"
        );
        let actual = step("atomic_step_context", BEFORE, MEMORY);
        add(
            &mut spec,
            &format!("atomic_step_by_law {PARAMS}"),
            &format!("@Eq ({CONFIG}) ({actual}) ({})", expected()),
            &format!("ir_byte_step_fetch_add_relaxed_u64_seq_below_v1 {args}"),
        );
        let run = format!(
            "ir_byte_run_v1 Nat atomic_step_context providers 1
  (@IRByteConfigV1.running Nat (atomic_step_machine {BEFORE}) {})",
            world(MEMORY)
        );
        add(
            &mut spec,
            &format!("atomic_step_run_by_law {PARAMS}"),
            &format!("@Eq ({CONFIG}) ({run}) ({})", expected()),
            &format!("ir_byte_run_fetch_add_relaxed_u64_seq_one_v1 {args}"),
        );
        let predicate = "(fun (c : IRByteConfigV1 Nat) =>
  @IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => Prop)
    (fun (s : IRMachine) (w : IRByteWorldV1 Nat) =>
      @Eq Bool (ir_byte_world_valid_v1 Nat s w) Bool.true)
    (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => False) c)";
        add(
            &mut spec,
            &format!("atomic_step_world_by_law {PARAMS}"),
            &format!("{predicate} ({actual})"),
            &format!("ir_byte_step_fetch_add_relaxed_u64_seq_world_v1 {args}"),
        );
        let read = |base| {
            format!(
                "ir_byte_read_word_v1
  (ir_byte_mem_bytes_v1 (ir_byte_world_memory_v1 Nat
    (ir_byte_final_world_v1 Nat ({actual})))) 8 {base}"
            )
        };
        add(
            &mut spec,
            &format!("atomic_step_new_by_law {PARAMS}"),
            &format!("@Eq (IROption Nat) ({}) (@IROption.some Nat 42)", read(16)),
            &format!("ir_byte_step_fetch_add_relaxed_u64_seq_new_v1 {args}"),
        );
        add(
            &mut spec,
            &format!("atomic_step_frame_by_law {PARAMS}"),
            &format!("@Eq (IROption Nat) ({}) (@IROption.some Nat 77)", read(32)),
            &format!(
                "ir_byte_step_fetch_add_relaxed_u64_seq_frame_v1 {args} 32 8
  (@Or.inr (Nat.le (Nat.add 32 8) 16) (Nat.le (Nat.add 16 8) 32)
    (Nat.le_add_right 24 8))"
            ),
        );
        let changed = step(
            &context(
                INSTRUCTION,
                "(@IRList.cons Nat 100 (@IRList.nil Nat))",
                RESULT_TYPES,
                2,
            ),
            BEFORE,
            MEMORY,
        );
        reject(
            &mut spec,
            "atomic_step_law_wrong_destination",
            &changed,
            &expected(),
            "atomic_step_by_law providers bytes host",
        );
    });
}

#[test]
fn byte_atomic_instruction_remains_refused_by_legacy_execution() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        equality(
            &mut spec,
            "atomic_step_legacy_refusal",
            "IRConfig",
            &format!(
                "ir_exec (ir_byte_context_module_v1 atomic_step_context)
  ({INSTRUCTION}) {RESULTS} (atomic_step_machine {BEFORE})"
            ),
            "IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)",
        );
    });
}

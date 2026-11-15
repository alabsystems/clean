// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Executed sequential fetch-add fixtures, not an atomic/concurrent Arc claim.

use crate::spec::{SpecError, Specification};
use clean_kernel::Name;

#[test]
fn sequential_fetch_add_keeps_resource_failures_distinct_from_rejected_proofs() {
    let error = super::eval_ir_byte_atomic::with_declaration_name(
        "outer",
        SpecError::DeclarationBudgetExhausted {
            declaration: "interrupted_proof".into(),
            limit: 17,
        },
    );
    assert!(
        matches!(error, SpecError::DeclarationBudgetExhausted { declaration, limit: 17 }
        if declaration == "interrupted_proof")
    );
}

fn checked(spec: &Specification, name: &str) {
    let declaration = spec.get_definition(name).expect("installed declaration");
    assert!(!declaration.is_axiom && declaration.elaborated_value.is_some());
    spec.verify_definition(name).expect("kernel-checked proof");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn register(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Sequential fetch-add test fixture")
        .expect("fixture elaborates and checks");
}

fn check(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    register(
        spec,
        &format!("def {name} : Eq ({ty}) ({actual}) ({expected}) := Eq.refl ({ty}) ({expected})"),
    );
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, ty: &str, actual: &str, wrong: &str) {
    let source = format!("def {name} : Eq ({ty}) ({actual}) ({wrong}) := Eq.refl ({ty}) ({wrong})");
    let error = spec
        .add_recursive_def(&source, "Deliberately false fetch-add observation")
        .expect_err("false observation must fail");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn fixture() -> Specification {
    let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("actual public byte-profile registration");
    for source in [
        r"def fetch_test_ctx : IRByteContextV1 := IRByteContextV1.mk
  (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal))
  (IRList.cons IRByteLayoutV1
    (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (IRList.nil IRTy) (IRList.nil Nat))
    (IRList.nil IRByteLayoutV1))
  (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1)",
        r"def fetch_test_allocs : IRList IRByteAllocationV1 :=
  IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 32 7 Bool.true)
    (IRList.nil IRByteAllocationV1)",
        r"def fetch_test_blank : Nat -> IROption Nat := fun (_ : Nat) => IROption.none Nat",
        r"def fetch_test_memory (n : Nat) : IRByteMemoryV1 :=
  IRByteMemoryV1.mk fetch_test_allocs
    (ir_byte_write_word_v1
      (ir_byte_write_word_v1 fetch_test_blank 32 8 77) 16 8 n) 128",
        r"def fetch_test_operation (n delta : Nat) : IRByteMemoryResultV1 :=
  ir_byte_fetch_add_relaxed_u64_seq_v1 fetch_test_ctx
    (IRScalar.ptr_ 16) (IRScalar.int_ delta) (fetch_test_memory n)",
        r"def fetch_test_read (r : IRByteMemoryResultV1) (base size : Nat) : IROption Nat :=
  ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 r)) size base",
    ] {
        register(&mut spec, source);
    }
    spec
}

#[test]
fn public_sequential_fetch_add_laws_are_checked_without_axioms() {
    crate::test_utils::run_with_stack(|| {
        let spec = fixture();
        for name in [
            "ir_byte_fetch_add_relaxed_u64_seq_v1",
            "ir_byte_u64_rep_v1",
            "ir_byte_fetch_add_relaxed_u64_seq_below_v1",
            "ir_byte_fetch_add_relaxed_u64_seq_old_v1",
            "ir_byte_fetch_add_relaxed_u64_seq_new_v1",
            "ir_byte_fetch_add_relaxed_u64_seq_allocations_v1",
            "ir_byte_fetch_add_relaxed_u64_seq_cursor_v1",
            "ir_byte_fetch_add_relaxed_u64_seq_frame_v1",
        ] {
            checked(&spec, name);
        }
    });
}

#[test]
fn sequential_fetch_add_representation_premises_have_a_real_symbolic_witness() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        register(
            &mut spec,
            r"def fetch_test_symbolic_memory
  (bytes : Nat -> IROption Nat) (n : Nat) : IRByteMemoryV1 :=
IRByteMemoryV1.mk fetch_test_allocs (ir_byte_write_word_v1 bytes 16 8 n) 128",
        );
        register(
            &mut spec,
            r"def fetch_test_symbolic_41_to_42 (bytes : Nat -> IROption Nat) :
Eq IRByteMemoryResultV1
  (ir_byte_fetch_add_relaxed_u64_seq_v1 fetch_test_ctx (IRScalar.ptr_ 16) (IRScalar.int_ 1)
    (fetch_test_symbolic_memory bytes 41))
  (IRByteMemoryResultV1.value (IRScalar.int_ 41)
    (IRByteMemoryV1.mk fetch_test_allocs
      (ir_byte_write_word_v1 (ir_byte_write_word_v1 bytes 16 8 41) 16 8 42) 128)) :=
ir_byte_fetch_add_relaxed_u64_seq_below_v1 fetch_test_ctx (fetch_test_symbolic_memory bytes 41) 16 41 1
  (Nat.le_add_right 17 18446744073709551599)
  (Eq.refl (IROption IRByteLayoutV1)
    (IROption.some IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (IRList.nil IRTy) (IRList.nil Nat))))
  (Eq.refl Bool Bool.true)
  (ir_byte_u64_rep_write_v1 (IRByteMemoryV1.mk fetch_test_allocs bytes 128) 16 41)
  (Nat.le_add_right 43 18446744073709551573)",
        );
        checked(&spec, "fetch_test_symbolic_41_to_42");
    });
}

#[test]
fn sequential_fetch_add_returns_old_stores_wrapped_new_and_preserves_frame() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (index, old, delta, new) in [
            (0, 0_u64, 1_u64, 1_u64),
            (1, 41, 1, 42),
            (2, 41, 2, 43),
            (3, 9223372036854775807, 1, 9223372036854775808),
            (4, u64::MAX, 1, 0),
        ] {
            let operation = format!("fetch_test_operation {old} {delta}");
            check(
                &mut spec,
                &format!("fetch_old_{index}"),
                "IROption IRScalar",
                &format!("ir_byte_fetch_add_old_v1 ({operation})"),
                &format!("IROption.some IRScalar (IRScalar.int_ {old})"),
            );
            check(
                &mut spec,
                &format!("fetch_new_{index}"),
                "IROption Nat",
                &format!("fetch_test_read ({operation}) 16 8"),
                &format!("IROption.some Nat {new}"),
            );
            check(
                &mut spec,
                &format!("fetch_neighbor_{index}"),
                "IROption Nat",
                &format!("fetch_test_read ({operation}) 32 8"),
                "IROption.some Nat 77",
            );
            check(
                &mut spec,
                &format!("fetch_undefined_frame_{index}"),
                "IROption Nat",
                &format!("fetch_test_read ({operation}) 24 8"),
                "IROption.none Nat",
            );
            check(
                &mut spec,
                &format!("fetch_cursor_{index}"),
                "Nat",
                &format!("ir_byte_mem_next_v1 (ir_byte_fetch_add_memory_v1 ({operation}))"),
                "128",
            );
            check(
                &mut spec,
                &format!("fetch_allocations_{index}"),
                "IRList IRByteAllocationV1",
                &format!("ir_byte_mem_allocs_v1 (ir_byte_fetch_add_memory_v1 ({operation}))"),
                "fetch_test_allocs",
            );
        }
    });
}

#[test]
fn sequential_fetch_add_faults_preserve_the_original_memory() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (index, ptr, delta, mem, fault) in [
            (
                0,
                "IRScalar.ptr_ 17",
                "IRScalar.int_ 1",
                "fetch_test_memory 41",
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                1,
                "IRScalar.ptr_ 48",
                "IRScalar.int_ 1",
                "fetch_test_memory 41",
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                2,
                "IRScalar.nullptr_",
                "IRScalar.int_ 1",
                "fetch_test_memory 41",
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                3,
                "IRScalar.int_ 16",
                "IRScalar.int_ 1",
                "fetch_test_memory 41",
                "IROutcome.type_error IRFault.not_ptr",
            ),
            (
                4,
                "IRScalar.ptr_ 24",
                "IRScalar.int_ 1",
                "fetch_test_memory 41",
                "IROutcome.ub IRFault.uninit",
            ),
            (
                5,
                "IRScalar.ptr_ 16",
                "IRScalar.bool_ Bool.true",
                "fetch_test_memory 41",
                "IROutcome.type_error IRFault.width_bounded",
            ),
            (
                6,
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 18446744073709551616",
                "fetch_test_memory 41",
                "IROutcome.type_error IRFault.width_bounded",
            ),
            (
                7,
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 1",
                "ir_byte_retire_v1 7 (fetch_test_memory 41)",
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                8,
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 1",
                "IRByteMemoryV1.mk fetch_test_allocs (fun (_ : Nat) => IROption.some Nat 256) 128",
                "IROutcome.ub IRFault.uninit",
            ),
            (
                9,
                "IRScalar.ptr_ 18446744073709551616",
                "IRScalar.int_ 1",
                "fetch_test_memory 41",
                "IROutcome.type_error IRFault.not_ptr",
            ),
        ] {
            let operation = format!(
                "ir_byte_fetch_add_relaxed_u64_seq_v1 fetch_test_ctx ({ptr}) ({delta}) ({mem})"
            );
            check(
                &mut spec,
                &format!("fetch_fault_{index}"),
                "IRByteMemoryResultV1",
                &operation,
                &format!("IRByteMemoryResultV1.fault ({fault}) ({mem})"),
            );
            check(
                &mut spec,
                &format!("fetch_fault_memory_{index}"),
                "IRByteMemoryV1",
                &format!("ir_byte_fetch_add_memory_v1 ({operation})"),
                mem,
            );
        }
        for (index, layouts, fault) in [
            (0, "IRList.nil IRByteLayoutV1", "IROutcome.unmodelled IRFault.width_bounded"),
            (1, "IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.uint_ 64) 4 8 (IRList.nil IRTy) (IRList.nil Nat)) (IRList.nil IRByteLayoutV1)", "IROutcome.type_error IRFault.width_bounded"),
        ] {
            let ctx = format!("IRByteContextV1.mk (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal)) ({layouts}) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1)");
            check(&mut spec, &format!("fetch_layout_fault_{index}"), "IRByteMemoryResultV1",
                &format!("ir_byte_fetch_add_relaxed_u64_seq_v1 ({ctx}) (IRScalar.ptr_ 16) (IRScalar.int_ 1) (fetch_test_memory 41)"),
                &format!("IRByteMemoryResultV1.fault ({fault}) (fetch_test_memory 41)"));
        }
    });
}

#[test]
fn sequential_fetch_add_wrong_observations_fail_for_type_mismatch() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (name, ty, actual, wrong) in [
            (
                "fetch_wrong_return",
                "IROption IRScalar",
                "ir_byte_fetch_add_old_v1 (fetch_test_operation 41 1)",
                "IROption.some IRScalar (IRScalar.int_ 42)",
            ),
            (
                "fetch_wrong_increment",
                "IROption Nat",
                "fetch_test_read (fetch_test_operation 41 1) 16 8",
                "IROption.some Nat 43",
            ),
            (
                "fetch_wrong_stale",
                "IROption Nat",
                "fetch_test_read (fetch_test_operation 41 1) 16 8",
                "IROption.some Nat 41",
            ),
            (
                "fetch_wrong_address",
                "IROption Nat",
                "fetch_test_read (fetch_test_operation 41 1) 24 8",
                "IROption.some Nat 42",
            ),
            (
                "fetch_wrong_frame",
                "IROption Nat",
                "fetch_test_read (fetch_test_operation 41 1) 32 8",
                "IROption.some Nat 78",
            ),
            (
                "fetch_wrong_wrap",
                "IROption Nat",
                "fetch_test_read (fetch_test_operation 18446744073709551615 1) 16 8",
                "IROption.some Nat 18446744073709551616",
            ),
        ] {
            reject(&mut spec, name, ty, actual, wrong);
        }
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Model execution controls, not source attachment or concurrent atomicity.

use crate::spec::Specification;
use clean_kernel::Name;

#[path = "eval_ir_byte_usize_tests/step.rs"]
mod step;

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("registered definition");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("kernel-checked definition");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn register(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Distinct Usize byte-profile fixture")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
}

fn check(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    register(
        spec,
        &format!("def {name} : @Eq ({ty}) ({actual}) ({expected}) := @Eq.refl ({ty}) ({expected})"),
    );
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, ty: &str, actual: &str, wrong: &str) {
    let source =
        format!("def {name} : @Eq ({ty}) ({actual}) ({wrong}) := @Eq.refl ({ty}) ({wrong})");
    let error = spec
        .add_recursive_def(&source, "Deliberately false Usize endpoint")
        .expect_err("wrong endpoint must not check");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn fixture() -> Specification {
    let mut spec =
        crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public ByteV1 constructor");
    for source in [
        r"def usize_context (ty : IRTy) (size align : Nat) : IRByteContextV1 :=
IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))
  (@IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk ty size align (@IRList.nil IRTy) (@IRList.nil Nat)) (@IRList.nil IRByteLayoutV1))
  (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)",
        "def usize_ctx : IRByteContextV1 := usize_context (IRTy.usize_ 64) 8 8",
        r"def usize_allocs : IRList IRByteAllocationV1 :=
@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 32 7 Bool.true) (@IRList.nil IRByteAllocationV1)",
        "def usize_blank : Nat -> IROption Nat := fun (_ : Nat) => @IROption.none Nat",
        r"def usize_memory (n : Nat) : IRByteMemoryV1 := IRByteMemoryV1.mk usize_allocs
  (ir_byte_write_word_v1 (ir_byte_write_word_v1 usize_blank 32 8 77) 16 8 n) 128",
        r"def usize_op (n delta : Nat) : IRByteMemoryResultV1 :=
ir_byte_fetch_add_relaxed_usize_seq_v1 64 usize_ctx (IRScalar.ptr_ 16) (IRScalar.int_ delta) (usize_memory n)",
    ] {
        register(&mut spec, source);
    }
    spec
}

#[test]
fn byte_usize_type_width_and_constants_are_distinct_and_legacy_stays_refused() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (name, expression, expected) in [
            ("same", "ir_byte_ty_eq_v1 (IRTy.usize_ 64) (IRTy.usize_ 64)", "Bool.true"),
            ("not_u64", "ir_byte_ty_eq_v1 (IRTy.usize_ 64) (IRTy.uint_ 64)", "Bool.false"),
            ("not_width32", "ir_byte_ty_eq_v1 (IRTy.usize_ 64) (IRTy.usize_ 32)", "Bool.false"),
            ("fits_max", "ir_byte_value_matches_v1 usize_ctx (IRTy.usize_ 64) (IRScalar.int_ 18446744073709551615)", "Bool.true"),
            ("too_large", "ir_byte_value_matches_v1 usize_ctx (IRTy.usize_ 64) (IRScalar.int_ 18446744073709551616)", "Bool.false"),
            ("width32", "ir_byte_value_matches_v1 usize_ctx (IRTy.usize_ 32) (IRScalar.int_ 1)", "Bool.false"),
            ("pointer", "ir_byte_value_matches_v1 usize_ctx (IRTy.usize_ 64) (IRScalar.ptr_ 16)", "Bool.false"),
        ] {
            check(&mut spec, &format!("usize_type_{name}"), "Bool", expression, expected);
        }
        check(
            &mut spec,
            "usize_constant",
            "IRStepResult",
            "ir_byte_const_eval_v1 (IRTy.usize_ 64) (IRConst.int_ 7)",
            "IRStepResult.value (IRScalar.int_ 7)",
        );
        check(
            &mut spec,
            "usize_constant_wrap",
            "IRStepResult",
            "ir_byte_const_eval_v1 (IRTy.usize_ 64) (IRConst.int_ 18446744073709551616)",
            "IRStepResult.value (IRScalar.int_ 0)",
        );
        check(
            &mut spec,
            "usize_constant_wrong_width",
            "IRStepResult",
            "ir_byte_const_eval_v1 (IRTy.usize_ 32) (IRConst.int_ 7)",
            "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)",
        );
        for (name, expression) in [
            (
                "constant",
                "ir_const_eval (IRTy.usize_ 64) (IRConst.int_ 7)",
            ),
            (
                "arithmetic",
                "ir_binop_eval IRBinOp.add (IRTy.usize_ 64) (IRScalar.int_ 1) (IRScalar.int_ 2)",
            ),
        ] {
            check(
                &mut spec,
                &format!("usize_legacy_{name}"),
                "IRStepResult",
                expression,
                "IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            );
        }
        for bits in [0, 32, 64, 128] {
            let source = format!("def usize_legacy_atomic_{bits} (m : IRModule) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq {bits} 40 78) (@IRList.cons Nat 99 (@IRList.nil Nat)) s) (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)) := ir_exec_atomic_fetch_add_relaxed_usize_seq_unmodelled m {bits} 40 78 (@IRList.cons Nat 99 (@IRList.nil Nat)) s");
            register(&mut spec, &source);
            checked(&spec, &format!("usize_legacy_atomic_{bits}"));
        }
    });
}

#[test]
fn byte_usize_atomic_keeps_old_result_and_exact_memory_including_wrap() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (name, old, delta, new) in [("bounded", 41, 7, 48), ("wrap", u64::MAX, 1, 0)] {
            let actual = format!("usize_op {old} {delta}");
            let memory = format!("IRByteMemoryV1.mk usize_allocs (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 (usize_memory {old})) 16 8 {new}) 128");
            let expected = format!("IRByteMemoryResultV1.value (IRScalar.int_ {old}) ({memory})");
            check(
                &mut spec,
                &format!("usize_atomic_{name}"),
                "IRByteMemoryResultV1",
                &actual,
                &expected,
            );
            check(&mut spec, &format!("usize_frame_{name}"), "IROption Nat",
                &format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 ({actual}))) 8 32"),
                "@IROption.some Nat 77");
            reject(
                &mut spec,
                &format!("usize_wrong_old_{name}"),
                "IRByteMemoryResultV1",
                &actual,
                &format!("IRByteMemoryResultV1.value (IRScalar.int_ {new}) ({memory})"),
            );
            reject(
                &mut spec,
                &format!("usize_stale_{name}"),
                "IRByteMemoryResultV1",
                &actual,
                &format!("IRByteMemoryResultV1.value (IRScalar.int_ {old}) (usize_memory {old})"),
            );
        }
    });
}

#[test]
fn byte_usize_atomic_refuses_wrong_width_type_layout_and_memory() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for bits in [0, 8, 32, 128] {
            check(&mut spec, &format!("usize_width_{bits}"), "IRByteMemoryResultV1",
                &format!("ir_byte_fetch_add_relaxed_usize_seq_v1 {bits} usize_ctx (IRScalar.ptr_ 16) (IRScalar.int_ 7) (usize_memory 41)"),
                "IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) (usize_memory 41)");
        }
        for (name, context, pointer, value, memory, outcome) in [
            (
                "wrong_type",
                "usize_ctx",
                "IRScalar.ptr_ 16",
                "IRScalar.bool_ Bool.true",
                "usize_memory 41",
                "IROutcome.type_error IRFault.width_bounded",
            ),
            (
                "uninit",
                "usize_ctx",
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 7",
                "IRByteMemoryV1.mk usize_allocs usize_blank 128",
                "IROutcome.ub IRFault.uninit",
            ),
            (
                "misaligned",
                "usize_ctx",
                "IRScalar.ptr_ 17",
                "IRScalar.int_ 7",
                "usize_memory 41",
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                "outside",
                "usize_ctx",
                "IRScalar.ptr_ 48",
                "IRScalar.int_ 7",
                "usize_memory 41",
                "IROutcome.ub IRFault.bad_addr",
            ),
        ] {
            check(&mut spec, &format!("usize_refuse_{name}"), "IRByteMemoryResultV1",
                &format!("ir_byte_fetch_add_relaxed_usize_seq_v1 64 ({context}) ({pointer}) ({value}) ({memory})"),
                &format!("IRByteMemoryResultV1.fault ({outcome}) ({memory})"));
        }
        // Distinct layout keys are material: an otherwise valid U64 row does
        // not supply a Usize row. Refuse success, not merely a particular text.
        for (name, ctx) in [
            ("u64_layout", "usize_context (IRTy.uint_ 64) 8 8"),
            ("width32_layout", "usize_context (IRTy.usize_ 32) 8 8"),
            ("size", "usize_context (IRTy.usize_ 64) 4 8"),
        ] {
            reject(&mut spec, &format!("usize_reject_{name}"), "IROption IRScalar",
                &format!("ir_byte_fetch_add_old_v1 (ir_byte_fetch_add_relaxed_usize_seq_v1 64 ({ctx}) (IRScalar.ptr_ 16) (IRScalar.int_ 7) (usize_memory 41))"),
                "@IROption.some IRScalar (IRScalar.int_ 41)");
        }
    });
}

#[test]
fn byte_usize_representation_laws_have_no_axioms_or_success_premises() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for root in [
            "ir_byte_usize64_rep_write_v1",
            "ir_byte_usize64_rep_read_v1",
            "ir_byte_fetch_add_relaxed_usize64_seq_below_v1",
            "ir_byte_fetch_add_relaxed_usize64_seq_old_v1",
            "ir_byte_fetch_add_relaxed_usize64_seq_new_v1",
            "ir_byte_fetch_add_relaxed_usize64_seq_allocations_v1",
            "ir_byte_fetch_add_relaxed_usize64_seq_cursor_v1",
            "ir_byte_fetch_add_relaxed_usize64_seq_frame_v1",
            "ir_byte_step_fetch_add_relaxed_usize64_seq_below_v1",
            "ir_byte_run_fetch_add_relaxed_usize64_seq_one_v1",
            "ir_byte_step_fetch_add_relaxed_usize64_seq_world_v1",
            "ir_byte_step_fetch_add_relaxed_usize64_seq_new_v1",
            "ir_byte_step_fetch_add_relaxed_usize64_seq_frame_v1",
        ] {
            checked(&spec, root);
        }
        register(
            &mut spec,
            r"def usize_inhabited_primitive :
@Eq IRByteMemoryResultV1 (usize_op 41 7)
  (IRByteMemoryResultV1.value (IRScalar.int_ 41)
    (IRByteMemoryV1.mk usize_allocs (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 (usize_memory 41)) 16 8 48) 128)) :=
ir_byte_fetch_add_relaxed_usize64_seq_below_v1 usize_ctx (usize_memory 41) 16 41 7
  (Nat.le_add_right 17 18446744073709551599)
  (@Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.usize_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))))
  (@Eq.refl Bool Bool.true)
  (ir_byte_usize64_rep_write_v1 (IRByteMemoryV1.mk usize_allocs (ir_byte_write_word_v1 usize_blank 32 8 77) 128) 16 41)
  (Nat.le_add_right 49 18446744073709551567)",
        );
        checked(&spec, "usize_inhabited_primitive");
    });
}

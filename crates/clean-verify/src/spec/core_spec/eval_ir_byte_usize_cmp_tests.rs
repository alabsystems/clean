// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual ByteV1 dispatch/proof controls, not a Rust Arc or abort model.

use crate::spec::Specification;
use clean_kernel::Name;

#[path = "eval_ir_byte_usize_cmp_tests/step.rs"]
mod step;

#[path = "eval_ir_byte_usize_cmp_tests/pointer.rs"]
mod pointer;

#[path = "eval_ir_byte_usize_cmp_tests/scalar.rs"]
mod scalar;

const MAX: u64 = 9_223_372_036_854_775_807;
const ROOTS: &[&str] = &[
    "ir_byte_icmp_usize64_ugt_canonical_v1",
    "ir_byte_icmp_usize64_ugt_le_v1",
    "ir_byte_icmp_usize64_ugt_lt_v1",
    "ir_byte_step_icmp_usize64_ugt_v1",
    "ir_byte_run_icmp_usize64_ugt_one_v1",
    "ir_byte_step_icmp_usize64_ugt_world_v1",
];

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("registered definition");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).expect("kernel acceptance");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn register(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Usize comparison execution fixture")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
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
        .add_recursive_def(&source, "Deliberately wrong comparison endpoint")
        .expect_err("wrong endpoint must fail");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn fixture() -> Specification {
    Specification::new_eval_ir_byte_prelude_spec_v1().expect("actual public ByteV1 constructor")
}

fn comparison(op: &str, ty: &str, left: &str, right: &str) -> String {
    format!("ir_byte_icmp_eval_v1 IRICmpOp.{op} ({ty}) ({left}) ({right})")
}

#[test]
fn byte_usize_cmp_canonical_laws_and_strict_boundary_are_kernel_checked() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for root in ROOTS {
            checked(&spec, root);
        }
        for (suffix, old, value, order_proof, law) in [
            (
                "below",
                MAX - 1,
                "Bool.false",
                format!(
                    "@Nat.le.step {} {} (@Nat.le.refl {})",
                    MAX - 1,
                    MAX - 1,
                    MAX - 1
                ),
                "le",
            ),
            (
                "equal",
                MAX,
                "Bool.false",
                format!("@Nat.le.refl {MAX}"),
                "le",
            ),
            (
                "above",
                MAX + 1,
                "Bool.true",
                format!("@Nat.le.refl {}", MAX + 1),
                "lt",
            ),
        ] {
            let actual = comparison(
                "ugt",
                "IRTy.usize_ 64",
                &format!("IRScalar.int_ {old}"),
                &format!("IRScalar.int_ {MAX}"),
            );
            let expected = format!("IRStepResult.value (IRScalar.bool_ {value})");
            check(
                &mut spec,
                &format!("cmp_{suffix}_compute"),
                "IRStepResult",
                &actual,
                &expected,
            );
            register(&mut spec, &format!("def cmp_{suffix}_ordered_law : Eq IRStepResult ({actual}) ({expected}) :=
ir_byte_icmp_usize64_ugt_{law}_v1 {old} {MAX} (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) ({order_proof})"));
            checked(&spec, &format!("cmp_{suffix}_ordered_law"));
            register(&mut spec, &format!("def cmp_{suffix}_canonical_law : Eq IRStepResult ({actual}) ({expected}) :=
ir_byte_icmp_usize64_ugt_canonical_v1 {old} {MAX} (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)"));
            checked(&spec, &format!("cmp_{suffix}_canonical_law"));
        }
    });
}

#[test]
fn byte_usize_cmp_nominal_width_opcode_and_legacy_boundaries_stay_closed() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let not_int = "IRStepResult.fault (IROutcome.type_error IRFault.not_int)";
        let unsupported = "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)";
        for bits in [0, 8, 32, 128] {
            check(
                &mut spec,
                &format!("cmp_width_{bits}"),
                "IRStepResult",
                &comparison(
                    "ugt",
                    &format!("IRTy.usize_ {bits}"),
                    "IRScalar.int_ 8",
                    "IRScalar.int_ 7",
                ),
                unsupported,
            );
        }
        for (op, expected) in [
            ("eq_", false),
            ("ne_", true),
            ("ult", false),
            ("ule", false),
            ("uge", true),
            ("slt", false),
            ("sle", false),
            ("sgt", true),
            ("sge", true),
        ] {
            check(
                &mut spec,
                &format!("cmp_opcode_{op}"),
                "IRStepResult",
                &comparison(op, "IRTy.usize_ 64", "IRScalar.int_ 8", "IRScalar.int_ 7"),
                &format!("IRStepResult.value (IRScalar.bool_ Bool.{expected})"),
            );
            check(
                &mut spec,
                &format!("cmp_legacy_opcode_{op}"),
                "IRStepResult",
                &format!(
                    "ir_icmp_eval IRICmpOp.{op} (IRTy.usize_ 64) (IRScalar.int_ 8) (IRScalar.int_ 7)"
                ),
                not_int,
            );
        }
        for (suffix, left, right) in [
            ("left_pointer", "IRScalar.ptr_ 16", "IRScalar.int_ 7"),
            ("right_pointer", "IRScalar.int_ 8", "IRScalar.ptr_ 16"),
            ("bool", "IRScalar.bool_ Bool.true", "IRScalar.int_ 7"),
        ] {
            check(
                &mut spec,
                &format!("cmp_carrier_{suffix}"),
                "IRStepResult",
                &comparison("ugt", "IRTy.usize_ 64", left, right),
                not_int,
            );
        }
        check(
            &mut spec,
            "cmp_legacy_refusal",
            "IRStepResult",
            "ir_icmp_eval IRICmpOp.ugt (IRTy.usize_ 64) (IRScalar.int_ 8) (IRScalar.int_ 7)",
            not_int,
        );
        check(
            &mut spec,
            "cmp_nominal_not_alias",
            "Bool",
            "ir_byte_ty_eq_v1 (IRTy.usize_ 64) (IRTy.uint_ 64)",
            "Bool.false",
        );
        check(
            &mut spec,
            "cmp_uint_preserved",
            "IRStepResult",
            &comparison("uge", "IRTy.uint_ 64", "IRScalar.int_ 7", "IRScalar.int_ 7"),
            "IRStepResult.value (IRScalar.bool_ Bool.true)",
        );
    });
}

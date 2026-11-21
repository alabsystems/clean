// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::{word_and_loop, word_and_scalar, word_xor};
use crate::spec::{SpecError, Specification};
use clean_kernel::{BinderInfo, Declaration, Expr, Level, Name};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn application(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name), args)
}

fn with_input_bounds(result: Expr) -> Expr {
    // Independently bind width,a,b,aBound,bBound in that order.
    let b_bound = application(
        "Nat.lt",
        [Expr::bvar(1), application("ir_nat_pow2", [Expr::bvar(3)])],
    );
    let a_bound = application(
        "Nat.lt",
        [Expr::bvar(1), application("ir_nat_pow2", [Expr::bvar(2)])],
    );
    let result = Expr::pi(
        BinderInfo::Default,
        a_bound,
        Expr::pi(BinderInfo::Default, b_bound, result),
    );
    (0..3).fold(result, |body, _| {
        Expr::pi(BinderInfo::Default, constant("Nat"), body)
    })
}

fn expected_typed_and_telescope(carrier: &str) -> Expr {
    let actual = application(
        "ir_binop_eval",
        [
            constant("IRBinOp.and_"),
            application(carrier, [Expr::bvar(4)]),
            application("IRScalar.int_", [Expr::bvar(3)]),
            application("IRScalar.int_", [Expr::bvar(2)]),
        ],
    );
    let result = application(
        "IRStepResult.value",
        [application(
            "IRScalar.int_",
            [application("Nat.land", [Expr::bvar(3), Expr::bvar(2)])],
        )],
    );
    with_input_bounds(Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [constant("IRStepResult"), actual, result],
    ))
}

fn owner() -> Specification {
    crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
        .expect("actual public canonical arithmetic owner")
}

#[test]
fn canonical_and_bit_basis_replays_actual_stored_declarations_and_closures() {
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        for (root, source) in word_xor::LAWS
            .iter()
            .chain(word_and_loop::LAWS)
            .chain(word_and_scalar::LAWS)
        {
            let metadata = spec.get_definition(root).expect("production metadata");
            let name = Name::from_string(root);
            let info = spec
                .env()
                .get_const(&name)
                .expect("actual stored declaration");
            let value = info.value.clone().expect("complete proof body");
            assert!(source.starts_with(&format!("def {root} ")));
            assert!(!metadata.is_axiom);
            assert_eq!(metadata.elaborated_type.as_ref(), Some(&info.type_));
            assert_eq!(metadata.elaborated_value.as_ref(), Some(&value));
            assert!(!info.type_.has_fvar_quick() && !info.type_.has_loose_bvars());
            assert!(!value.has_fvar_quick() && !value.has_loose_bvars());
            spec.env()
                .check_decl_readonly_strict(&Declaration::Definition {
                    name: name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value,
                    is_reducible: info.is_reducible,
                })
                .expect("strict complete stored-declaration replay");
            assert!(spec
                .env()
                .axiom_deps(&name)
                .expect("axiom closure")
                .is_empty());
            assert!(spec
                .env()
                .trust_marker_deps(&name)
                .expect("marker closure")
                .is_empty());
        }
        for root in word_xor::ROOTS
            .iter()
            .chain(word_and_loop::ROOTS)
            .chain(word_and_scalar::ROOTS)
        {
            assert!(super::verify_root(&spec, root)
                .expect("strict rooted actual consumer certification")
                .is_certified());
        }
    });
}

#[test]
fn canonical_and_scalar_actual_typed_operations_derive_result_and_bound_from_inputs() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = owner();
        for (carrier, theorem) in [
            ("uint_", "ir_byte_and_uint_canonical_v1"),
            ("int_", "ir_byte_and_int_canonical_v1"),
        ] {
            assert_eq!(
                spec.env()
                    .get_const(&Name::from_string(theorem))
                    .expect("actual stored typed law")
                    .type_,
                expected_typed_and_telescope(&format!("IRTy.{carrier}")),
                "exact actual opcode/carrier/operands and five-binder telescope"
            );
            let name = format!("and_actual_{carrier}_input_only");
            let actual = format!("ir_binop_eval IRBinOp.and_ (IRTy.{carrier} width) (IRScalar.int_ a) (IRScalar.int_ b)");
            let equality = format!(
                "@Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ (Nat.land a b)))"
            );
            let bound = "Nat.lt (Nat.land a b) (ir_nat_pow2 width)";
            let source = format!("def {name} (width a b : Nat) (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) : And ({equality}) ({bound}) := @And.intro ({equality}) ({bound}) ({theorem} width a b aBound bBound) (ir_byte_and_canonical_result_bound_v1 width a b aBound bBound)");
            spec.add_recursive_def(
                &source,
                "actual evaluator and derived output fit, only two input bounds",
            )
            .expect("complete typed AND law");
            super::verify_root(&spec, &name)
                .expect("strict rooted full actual-operation application");
        }
        assert_eq!(
            spec.env()
                .get_const(&Name::from_string("ir_byte_and_canonical_result_bound_v1"))
                .expect("actual derived bound")
                .type_,
            with_input_bounds(application(
                "Nat.lt",
                [
                    application("Nat.land", [Expr::bvar(3), Expr::bvar(2)]),
                    application("ir_nat_pow2", [Expr::bvar(4)])
                ]
            )),
            "the result bound is derived from the same two input bounds"
        );
    });
}

#[test]
fn canonical_and_scalar_refuses_changed_opcode_zero_width_carrier_and_missing_bound() {
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        let bounds =
            "(aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width))";
        for (label, actual) in [
            ("add", "ir_binop_eval IRBinOp.add (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b)"),
            ("zero_width", "ir_binop_eval IRBinOp.and_ (IRTy.uint_ 0) (IRScalar.int_ a) (IRScalar.int_ b)"),
            ("float", "ir_binop_eval IRBinOp.and_ (IRTy.float_ width) (IRScalar.int_ a) (IRScalar.int_ b)"),
        ] {
            let mut mutant = spec.clone();
            let source = format!("def and_scalar_wrong_{label} (width a b : Nat) {bounds} : @Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ (Nat.land a b))) := ir_byte_and_uint_canonical_v1 width a b aBound bBound");
            let error = mutant.add_recursive_def(&source, "false actual typed operation endpoint").expect_err("altered actual operation cannot retain the canonical proof");
            crate::test_utils::assert_type_mismatch_rejection(&error, "actual operation endpoint mutation");
            assert!(!matches!(error, SpecError::DeclarationBudgetExhausted { .. }), "budget exhaustion is not a rejection");
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        let mut mutant = spec.clone();
        let error = mutant.add_recursive_def("def and_scalar_missing_bound (width a b : Nat) (aBound : Nat.lt a (ir_nat_pow2 width)) : @Eq IRStepResult (ir_binop_eval IRBinOp.and_ (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b)) (IRStepResult.value (IRScalar.int_ (Nat.land a b))) := ir_byte_and_uint_canonical_v1 width a b aBound", "false unbounded operand claim").expect_err("both operand bounds must be present");
        crate::test_utils::assert_type_mismatch_rejection(
            &error,
            "actual operation endpoint mutation",
        );
        assert!(!matches!(
            error,
            SpecError::DeclarationBudgetExhausted { .. }
        ));
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
    });
}

#[test]
fn canonical_and_loop_checks_actual_width_recursion_and_truncation_boundaries() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = owner();
        for (name, source) in [
            ("and_loop_universal", "def and_loop_universal (fuel a b : Nat) : @Eq Nat (ir_nat_bitop_go Bool.and fuel a b) (Nat.bitwiseAux Bool.and fuel a b) := ir_and_loop_canonical_v1 fuel a b"),
            ("and_width_universal", "def and_width_universal (width a b : Nat) (aBound : Nat.lt a (Nat.pow 2 width)) (bBound : Nat.lt b (Nat.pow 2 width)) : @Eq Nat (ir_nat_bitop_go Bool.and width a b) (Nat.land a b) := ir_and_width_loop_canonical_v1 width a b aBound bBound"),
        ] {
            spec.add_recursive_def(source, "independent full telescope over actual bit loop").expect("universal actual-loop claim");
            super::verify_root(&spec, name).expect("strict rooted complete-loop claim");
        }
        for (index, (width, a, b, expected)) in [
            (0, 0, 0, 0),
            (0, 1, 0, 0),
            (1, 1, 1, 1),
            (4, 15, 1, 1),
            (8, 255, 128, 128),
        ]
        .into_iter()
        .enumerate()
        {
            let name = format!("and_loop_boundary_{index}");
            let source = format!("def {name} : @Eq Nat (ir_nat_bitop_go Bool.and {width} {a} {b}) {expected} := @Eq.trans Nat (ir_nat_bitop_go Bool.and {width} {a} {b}) (Nat.bitwiseAux Bool.and {width} {a} {b}) {expected} (ir_and_loop_canonical_v1 {width} {a} {b}) (@Eq.refl Nat {expected})");
            spec.add_recursive_def(
                &source,
                "actual loop, including zero-fuel truncation outside the operand bound",
            )
            .expect("ground boundary through universal loop proof");
            super::verify_root(&spec, &name).expect("strict boundary replay");
        }
    });
}

#[test]
fn canonical_and_loop_refuses_wrong_operation_fuel_and_missing_operand_bound() {
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        for source in [
            "def and_loop_wrong_operation (fuel a b : Nat) : @Eq Nat (ir_nat_bitop_go Bool.or fuel a b) (Nat.bitwiseAux Bool.and fuel a b) := ir_and_loop_canonical_v1 fuel a b",
            "def and_loop_wrong_fuel (fuel a b : Nat) : @Eq Nat (ir_nat_bitop_go Bool.and 0 a b) (Nat.bitwiseAux Bool.and fuel a b) := ir_and_loop_canonical_v1 fuel a b",
            "def and_loop_missing_bound (width a b : Nat) (aBound : Nat.lt a (Nat.pow 2 width)) : @Eq Nat (ir_nat_bitop_go Bool.and width a b) (Nat.land a b) := ir_and_loop_canonical_v1 width a b",
        ] {
            let mut mutant = spec.clone();
            let error = mutant.add_recursive_def(source, "false actual-loop endpoint").expect_err("wrong loop cannot reuse the original proof");
            crate::test_utils::assert_type_mismatch_rejection(&error, "actual operation endpoint mutation");
            assert!(!matches!(error, SpecError::DeclarationBudgetExhausted { .. }), "a resource stop is not a mathematical refusal");
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
    });
}

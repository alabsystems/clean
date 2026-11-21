// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::word_shl_canonical;
use clean_kernel::{BinderInfo, Declaration, Expr, Level, Name};
fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn expected_scalar_telescope() -> Expr {
    let width = Expr::bvar(5);
    let word = Expr::bvar(4);
    let amount = Expr::bvar(3);
    let actual = app(
        "ir_binop_eval",
        [
            c("IRBinOp.shl"),
            app("IRTy.uint_", [width.clone()]),
            app("IRScalar.int_", [word.clone()]),
            app("IRScalar.int_", [amount.clone()]),
        ],
    );
    let quotient = app(
        "ir_wrap",
        [
            width,
            app("ir_nat_mul", [word, app("ir_nat_pow2", [amount])]),
        ],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            c("IRStepResult"),
            actual,
            app("IRStepResult.value", [app("IRScalar.int_", [quotient])]),
        ],
    );
    let word_bound = app(
        "Nat.lt",
        [Expr::bvar(1), app("ir_nat_pow2", [Expr::bvar(2)])],
    );
    let amount_bound = app(
        "Nat.lt",
        [Expr::bvar(1), app("ir_nat_pow2", [Expr::bvar(3)])],
    );
    let in_range = app("Nat.lt", [Expr::bvar(2), Expr::bvar(4)]);
    let body = Expr::pi(
        BinderInfo::Default,
        word_bound,
        Expr::pi(
            BinderInfo::Default,
            amount_bound,
            Expr::pi(BinderInfo::Default, in_range, goal),
        ),
    );
    (0..3).fold(body, |body, _| {
        Expr::pi(BinderInfo::Default, c("Nat"), body)
    })
}
#[test]
fn canonical_shl_replays_actual_complete_stored_proofs_and_closures() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for (root, _) in word_shl_canonical::LAWS {
            let name = Name::from_string(root);
            let info = spec.env().get_const(&name).unwrap();
            spec.env()
                .check_decl_readonly_strict(&Declaration::Definition {
                    name: name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: info.value.clone().expect("complete actual proof"),
                    is_reducible: info.is_reducible,
                })
                .expect("strict full stored proof replay");
            assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
            assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
        }
        for root in word_shl_canonical::ROOTS {
            assert!(super::verify_root(&spec, root).unwrap().is_certified());
        }
    });
}
#[test]
fn canonical_shl_retains_independent_six_binder_contract_and_symbolic_application() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        assert_eq!(
            spec.env()
                .get_const(&Name::from_string("ir_byte_shl_uint_canonical_v1"))
                .unwrap()
                .type_,
            expected_scalar_telescope()
        );
        let source="def canonical_shl_symbolic (width word amount : Nat) (wordBound : Nat.lt word (ir_nat_pow2 width)) (amountBound : Nat.lt amount (ir_nat_pow2 width)) (inRange : Nat.lt amount width) : @Eq IRStepResult (ir_binop_eval IRBinOp.shl (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)) (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))) := ir_byte_shl_uint_canonical_v1 width word amount wordBound amountBound inRange";
        spec.add_recursive_def(
            source,
            "independent actual operation and derived bound telescope",
        )
        .unwrap();
        super::verify_root(&spec, "canonical_shl_symbolic").unwrap();
    });
}
#[test]
fn canonical_shl_matches_independent_word_boundary_answers_and_out_of_range_faults() {
    crate::test_utils::run_with_stack(super::word_shl_canonical_boundaries::check);
}
#[test]
fn canonical_shl_refuses_altered_opcode_carrier_width_and_missing_range() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        let bounds="(wordBound : Nat.lt word (ir_nat_pow2 width)) (amountBound : Nat.lt amount (ir_nat_pow2 width)) (inRange : Nat.lt amount width)";
        for (label,actual) in [
            ("right","ir_binop_eval IRBinOp.lshr (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)"),
            ("float","ir_binop_eval IRBinOp.shl (IRTy.float_ width) (IRScalar.int_ word) (IRScalar.int_ amount)"),
            ("zero_width","ir_binop_eval IRBinOp.shl (IRTy.uint_ 0) (IRScalar.int_ word) (IRScalar.int_ amount)"),
        ] {
            let source=format!("def canonical_shl_mutant_{label} (width word amount : Nat) {bounds} : @Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))) := ir_byte_shl_uint_canonical_v1 width word amount wordBound amountBound inRange");
            let mut mutant=spec.clone();let error=mutant.add_recursive_def(&source,"changed actual endpoint").expect_err("must reject original proof at altered endpoint");
            crate::test_utils::assert_type_mismatch_rejection(&error,"altered left shift endpoint");assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        let mut mutant = spec.clone();
        let error=mutant.add_recursive_def("def canonical_shl_missing_range (width word amount : Nat) (wordBound : Nat.lt word (ir_nat_pow2 width)) (amountBound : Nat.lt amount (ir_nat_pow2 width)) : @Eq IRStepResult (ir_binop_eval IRBinOp.shl (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)) (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))) := ir_byte_shl_uint_canonical_v1 width word amount wordBound amountBound","missing original range premise").expect_err("range cannot be omitted");
        crate::test_utils::assert_type_mismatch_rejection(&error, "missing left shift range");
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
    });
}

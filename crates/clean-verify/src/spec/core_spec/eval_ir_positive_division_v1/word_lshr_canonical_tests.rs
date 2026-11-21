// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::word_lshr_canonical;
use clean_kernel::{BinderInfo, Declaration, Expr, Level, Name};
fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn source_nat_literal(value: u64) -> Expr {
    // Independently retain the source numeral's exact checked Nat instance.
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            c("Nat"),
            Expr::nat_lit(value),
            app("instOfNatNat", [Expr::nat_lit(value)]),
        ],
    )
}
fn expected_scalar_telescope() -> Expr {
    let width = Expr::bvar(5);
    let word = Expr::bvar(4);
    let amount = Expr::bvar(3);
    let actual = app(
        "ir_binop_eval",
        [
            c("IRBinOp.lshr"),
            app("IRTy.uint_", [width]),
            app("IRScalar.int_", [word.clone()]),
            app("IRScalar.int_", [amount.clone()]),
        ],
    );
    let quotient = app(
        "Nat.div",
        [word, app("Nat.pow", [source_nat_literal(2), amount])],
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
fn canonical_lshr_replays_actual_complete_stored_proofs_and_closures() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for (root, _) in word_lshr_canonical::LAWS {
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
        for root in word_lshr_canonical::ROOTS {
            assert!(super::verify_root(&spec, root).unwrap().is_certified());
        }
    });
}
#[test]
fn canonical_lshr_retains_independent_six_binder_contract_and_symbolic_application() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        assert_eq!(
            spec.env()
                .get_const(&Name::from_string("ir_byte_lshr_uint_canonical_v1"))
                .unwrap()
                .type_,
            expected_scalar_telescope()
        );
        let source="def canonical_lshr_symbolic (width word amount : Nat) (wordBound : Nat.lt word (ir_nat_pow2 width)) (amountBound : Nat.lt amount (ir_nat_pow2 width)) (inRange : Nat.lt amount width) : And (@Eq IRStepResult (ir_binop_eval IRBinOp.lshr (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)) (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount))))) (Nat.lt (Nat.div word (Nat.pow 2 amount)) (ir_nat_pow2 width)) := @And.intro (@Eq IRStepResult (ir_binop_eval IRBinOp.lshr (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)) (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount))))) (Nat.lt (Nat.div word (Nat.pow 2 amount)) (ir_nat_pow2 width)) (ir_byte_lshr_uint_canonical_v1 width word amount wordBound amountBound inRange) (ir_byte_lshr_uint_canonical_result_bound_v1 width word amount wordBound)";
        spec.add_recursive_def(
            source,
            "independent actual operation and derived bound telescope",
        )
        .unwrap();
        super::verify_root(&spec, "canonical_lshr_symbolic").unwrap();
    });
}
#[test]
fn canonical_lshr_matches_independent_word_boundary_answers_and_out_of_range_faults() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for width in [32_u64, 64] {
            let limit = 1_u128 << width;
            let maximum = (limit - 1) as u64;
            for (index, (word, amount)) in [
                (0, 0),
                (maximum, 0),
                (maximum, width - 1),
                (1_u64 << (width - 1), width - 1),
                (maximum, 32 - 1),
            ]
            .into_iter()
            .enumerate()
            {
                let answer = word >> amount;
                let word_gap = limit - u128::from(word) - 1;
                let amount_gap = limit - u128::from(amount) - 1;
                let range_gap = width - amount - 1;
                let name = format!("canonical_lshr_ground_{width}_{index}");
                let actual=format!("ir_binop_eval IRBinOp.lshr (IRTy.uint_ {width}) (IRScalar.int_ {word}) (IRScalar.int_ {amount})");
                let canonical = format!(
                    "IRStepResult.value (IRScalar.int_ (Nat.div {word} (Nat.pow 2 {amount})))"
                );
                let source=format!("def {name} : @Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ {answer})) := @Eq.trans IRStepResult ({actual}) ({canonical}) (IRStepResult.value (IRScalar.int_ {answer})) (ir_byte_lshr_uint_canonical_v1 {width} {word} {amount} (@Nat.le_add_right (Nat.succ {word}) {word_gap}) (@Nat.le_add_right (Nat.succ {amount}) {amount_gap}) (@Nat.le_add_right (Nat.succ {amount}) {range_gap})) (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ {answer})))");
                spec.add_recursive_def(
                    &source,
                    "independent host answer, derived from actual operation",
                )
                .unwrap();
                super::verify_root(&spec, &name).unwrap();
            }
            let name = format!("canonical_lshr_range_fault_{width}");
            let source=format!("def {name} : @Eq IRStepResult (ir_binop_eval IRBinOp.lshr (IRTy.uint_ {width}) (IRScalar.int_ 7) (IRScalar.int_ {width})) (IRStepResult.fault (IROutcome.ub IRFault.shift_oob)) := @Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.shift_oob))");
            spec.add_recursive_def(&source, "amount equal to width remains an actual UB fault")
                .unwrap();
            super::verify_root(&spec, &name).unwrap();
        }
    });
}
#[test]
fn canonical_lshr_refuses_altered_opcode_carrier_width_and_missing_range() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        let bounds="(wordBound : Nat.lt word (ir_nat_pow2 width)) (amountBound : Nat.lt amount (ir_nat_pow2 width)) (inRange : Nat.lt amount width)";
        for (label,actual) in [
            ("left","ir_binop_eval IRBinOp.shl (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)"),
            ("float","ir_binop_eval IRBinOp.lshr (IRTy.float_ width) (IRScalar.int_ word) (IRScalar.int_ amount)"),
            ("zero_width","ir_binop_eval IRBinOp.lshr (IRTy.uint_ 0) (IRScalar.int_ word) (IRScalar.int_ amount)"),
        ] {
            let source=format!("def canonical_lshr_mutant_{label} (width word amount : Nat) {bounds} : @Eq IRStepResult ({actual}) (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount)))) := ir_byte_lshr_uint_canonical_v1 width word amount wordBound amountBound inRange");
            let mut mutant=spec.clone();let error=mutant.add_recursive_def(&source,"changed actual endpoint").expect_err("must reject original proof at altered endpoint");
            crate::test_utils::assert_type_mismatch_rejection(&error,"altered logical shift endpoint");assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        let mut mutant = spec.clone();
        let error=mutant.add_recursive_def("def canonical_lshr_missing_range (width word amount : Nat) (wordBound : Nat.lt word (ir_nat_pow2 width)) (amountBound : Nat.lt amount (ir_nat_pow2 width)) : @Eq IRStepResult (ir_binop_eval IRBinOp.lshr (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount)) (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount)))) := ir_byte_lshr_uint_canonical_v1 width word amount wordBound amountBound","missing original range premise").expect_err("range cannot be omitted");
        crate::test_utils::assert_type_mismatch_rejection(&error, "missing logical shift range");
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
    });
}

// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::canonical_division;
use crate::spec::SpecError;
use clean_kernel::{Declaration, Name};

#[test]
fn actual_canonical_division_replays_complete_stored_proofs_and_roots() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for (root, _) in canonical_division::LAWS {
            let name = Name::from_string(root);
            let info = spec
                .env()
                .get_const(&name)
                .expect("actual registered bridge");
            spec.env()
                .check_decl_readonly_strict(&Declaration::Definition {
                    name: name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: info.value.clone().expect("complete proof"),
                    is_reducible: info.is_reducible,
                })
                .expect("strict complete replay");
            assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
            assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
        }
        for root in canonical_division::ROOTS {
            assert!(super::verify_root(&spec, root).unwrap().is_certified());
        }
    });
}

#[test]
fn actual_canonical_division_keeps_host_quotient_and_remainder_boundaries() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for (index, (word, divisor)) in [(0_u64, 1_u64), (1, 1), (2, 3), (15, 3), (15, 4), (31, 16)]
            .into_iter()
            .enumerate()
        {
            let pred = divisor - 1;
            for (operation, canonical, law, answer) in [
                (
                    "ir_nat_div",
                    "Nat.div",
                    "ir_nat_div_canonical_positive_v1",
                    word / divisor,
                ),
                (
                    "ir_nat_rem",
                    "Nat.mod",
                    "ir_nat_rem_canonical_positive_v1",
                    word % divisor,
                ),
            ] {
                let name = format!("canonical_division_ground_{index}_{operation}");
                let source = format!("def {name} : @Eq Nat ({operation} {word} {divisor}) {answer} := @Eq.trans Nat ({operation} {word} {divisor}) ({canonical} {word} {divisor}) {answer} ({law} {word} {pred}) (@Eq.refl Nat {answer})");
                spec.add_recursive_def(&source, "independent host arithmetic answer")
                    .unwrap();
                super::verify_root(&spec, &name).expect("strict complete boundary proof");
            }
        }
    });
}

#[test]
fn actual_canonical_division_refuses_changed_divisor_and_unjustified_restoring_fuel() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for source in [
            "def canonical_divisor_mutant (word d : Nat) : @Eq Nat (ir_nat_div word (Nat.succ d)) (Nat.div word (Nat.succ (Nat.succ d))) := ir_nat_div_canonical_positive_v1 word d",
            "def canonical_restoring_fuel_mutant (word d fuel : Nat) (enough : @Eq Bool (ir_nat_ltb word (ir_nat_shl (Nat.succ d) fuel)) Bool.true) : @Eq Nat (ir_dm_quot (ir_dm_go 1 word 0 (Nat.succ d) (IRDivMod.mk word 0))) (Nat.div word (Nat.succ d)) := ir_dm_quot_canonical_positive_at_fuel_v1 word d fuel enough",
            "def canonical_restoring_missing_bound (word d fuel : Nat) : @Eq Nat (ir_dm_quot (ir_dm_go 1 word fuel (Nat.succ d) (IRDivMod.mk word 0))) (Nat.div word (Nat.succ d)) := ir_dm_quot_canonical_positive_at_fuel_v1 word d fuel",
        ] {
            let mut mutant = spec.clone();
            let error = mutant.add_recursive_def(source, "altered actual endpoint or omitted restoring premise").expect_err("original bridge cannot justify the altered contract");
            crate::test_utils::assert_type_mismatch_rejection(&error, "actual operation endpoint mutation");
            assert!(!matches!(error, SpecError::DeclarationBudgetExhausted { .. }));
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
    });
}

#[test]
fn actual_raw_zero_division_difference_does_not_grant_typed_success() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
        for (name,source) in [
            ("raw_zero_dividend","def raw_zero_dividend : @Eq Nat (ir_nat_div 7 0) 7 := @Eq.refl Nat 7"),
            ("canonical_zero_quotient","def canonical_zero_quotient : @Eq Nat (Nat.div 7 0) 0 := @Eq.refl Nat 0"),
            ("typed_zero_divisor_fault","def typed_zero_divisor_fault : @Eq IRStepResult (ir_binop_eval IRBinOp.udiv (IRTy.uint_ 64) (IRScalar.int_ 7) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.ub IRFault.div_zero)) := @Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.div_zero))"),
        ] {spec.add_recursive_def(source,"preserve actual zero-divisor behavior").unwrap();super::verify_root(&spec,name).unwrap();}
        let error=spec.add_recursive_def("def canonical_division_missing_positive (word divisor : Nat) : @Eq Nat (ir_nat_div word divisor) (Nat.div word divisor) := ir_nat_div_canonical_nonzero_v1 word divisor","positive premise cannot be omitted").expect_err("raw zero behavior precludes unbounded agreement");
        crate::test_utils::assert_type_mismatch_rejection(&error, "missing positive divisor");
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
    });
}

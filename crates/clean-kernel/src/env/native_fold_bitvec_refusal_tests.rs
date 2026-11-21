// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked BitVec definitions do not authorize Nat-valued native candidates.

use super::{c, n};
use crate::env::native_fold_authority::{FoldRefusal, FoldRole};
use crate::env::{Environment, KernelTheory};
use crate::expr::Expr;
use crate::tc::TypeChecker;

type Candidate = fn(&[&Expr]) -> Option<Expr>;

#[test]
fn test_checked_bitvec_arithmetic_native_candidates_remain_review_refused() {
    let env = Environment::try_with_prelude_uncached().expect("checked prelude");
    let operations: [(&str, Candidate); 2] = [
        (
            "BitVec.add",
            crate::env::native_reducers_bitvec::reduce_bitvec_add,
        ),
        (
            "BitVec.mul",
            crate::env::native_reducers_bitvec::reduce_bitvec_mul,
        ),
    ];
    for (head, candidate) in operations {
        let width = Expr::nat_lit(8);
        let operand = |value| Expr::apps(c("BitVec.ofNat"), [width.clone(), Expr::nat_lit(value)]);
        let left = operand(16);
        let right = operand(16);
        let application = Expr::apps(c(head), [width.clone(), left.clone(), right.clone()]);
        let raw = candidate(&[&width, &left, &right]).expect("candidate is actually exercised");
        let mut reference = TypeChecker::new(&env);
        reference.set_kernel_theory(KernelTheory::LeanReference);
        let raw_type = reference.infer_type(&raw).expect("native candidate type");
        let declared_type = reference
            .infer_type(&application)
            .expect("checked source application type");
        assert!(reference.is_def_eq(&raw_type, &c("Nat")));
        assert!(reference.is_def_eq(&declared_type, &Expr::app(c("BitVec"), width)));
        assert!(
            !reference.is_def_eq(&raw_type, &declared_type),
            "{head} must not erase its carrier"
        );
        assert!(
            matches!(
                env.native_fold_definition_verdict(&n(head)),
                Ok(("clean-prelude", FoldRole::Refused))
            ),
            "{head}: negative pin is a known definition, not a native permission"
        );
        assert!(env.native_fold_definition_admitted(&n(head)));
        for theory in [
            KernelTheory::Extended,
            KernelTheory::Lean,
            KernelTheory::LeanReference,
        ] {
            assert!(
                env.native_reducer_in(&n(head), theory).is_none(),
                "{head}: wrong candidate stays off in {theory:?}"
            );
        }
        assert!(
            matches!(
                env.native_fold_verdict(&n(head)),
                Err(FoldRefusal::ReviewRefused {
                    world: "clean-prelude"
                })
            ),
            "{head}: the measured wrong-type native rule must stay off"
        );
        let review = crate::env::native_fold_review::review(&env, &n(head), true);
        assert!(review.fired > 0 && !review.passed(), "{head}: {review:?}");
        assert!(
            review
                .failures
                .iter()
                .any(|failure| failure.starts_with(&format!("T {head} "))),
            "{head}: {review:?}"
        );
    }
}

#[test]
fn test_checked_bitvec_arithmetic_definitions_compute_without_native_permission() {
    let env = Environment::try_with_prelude_uncached().expect("checked prelude");
    let cases = [
        ("BitVec.add", 0, 1, 1, 0),
        ("BitVec.mul", 0, 1, 1, 0),
        ("BitVec.add", 8, 200, 100, 44),
        ("BitVec.mul", 8, 16, 16, 0),
        ("BitVec.add", 128, 200, 100, 300),
        ("BitVec.mul", 128, 16, 16, 256),
    ];
    for (head, width, left, right, answer) in cases {
        assert!(
            !env.native_fold_authorized(&n(head)),
            "{head} must compute through its definition"
        );
        let width = Expr::nat_lit(width);
        let value =
            |payload| Expr::apps(c("BitVec.ofNat"), [width.clone(), Expr::nat_lit(payload)]);
        let application = Expr::apps(c(head), [width.clone(), value(left), value(right)]);
        let expected = value(answer);
        let wrong_payload = value(answer + 1);
        let wrong_carrier = Expr::nat_lit(answer);
        // Both the reference checker and ordinary production checker must use
        // the stored typed definition, keeping the wrong native rule disabled.
        for theory in [None, Some(KernelTheory::LeanReference)] {
            let mut checker = TypeChecker::new(&env);
            if let Some(theory) = theory {
                checker.set_kernel_theory(theory);
            }
            let actual_type = checker
                .infer_type(&application)
                .expect("source result type");
            let expected_type = checker
                .infer_type(&expected)
                .expect("typed expected result");
            assert!(
                checker.is_def_eq(&actual_type, &expected_type),
                "{head}: result carrier"
            );
            assert!(
                checker.is_def_eq(&application, &expected),
                "{head}: checked wraparound value"
            );
            if width != Expr::nat_lit(0) {
                assert!(
                    !checker.is_def_eq(&application, &wrong_payload),
                    "{head}: false payload"
                );
            }
            assert!(
                !checker.is_def_eq(&application, &wrong_carrier),
                "{head}: bare Nat is not BitVec"
            );
        }
    }
}

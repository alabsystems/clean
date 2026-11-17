// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{roots, setup_world};
use super::*;
use clean_kernel::{BinderData, BinderInfo, LeanWorld, Multiplicity};

#[test]
fn test_replayed_context_non_lean_binder_multiplicities_are_refused() {
    let (_directory, program) = setup_world(LeanWorld::ORACLE);
    let context = program.replay_context(&roots()).unwrap();
    let leaf = Expr::const_(Name::from_string("Leaf"), vec![]);
    let query = context.declaration(&Name::from_string("query")).unwrap();
    for multiplicity in [Multiplicity::Many, Multiplicity::Zero, Multiplicity::One] {
        let binder = BinderData::new(BinderInfo::Default, multiplicity);
        let lambda = Expr::lam(binder, leaf.clone(), Expr::bvar(0));
        let pi = Expr::pi(binder, leaf.clone(), leaf.clone());
        let limits = ReplayContextLimits::default();
        assert!(!lambda.has_loose_bvars_quick());
        assert!(!pi.has_loose_bvars_quick());
        let expected = context.check_expected_type(&query, &[], &pi, limits);
        if multiplicity == Multiplicity::Many {
            expected.expect("ordinary Lean source query must retain its actual arrow type");
            for expression in [lambda, pi] {
                assert!(context
                    .definitionally_equal(&expression, &expression, limits)
                    .unwrap());
                drop(
                    context
                        .whnf_closed(&expression, limits)
                        .expect("ordinary Lean binder must remain admissible"),
                );
            }
        } else {
            assert!(matches!(
                expected,
                Err(ReplayContextError::ExtendedExpression)
            ));
            for expression in [lambda, pi] {
                assert!(matches!(
                    context.definitionally_equal(&expression, &expression, limits),
                    Err(ReplayContextError::ExtendedExpression)
                ));
                assert!(matches!(
                    context.whnf_closed(&expression, limits),
                    Err(ReplayContextError::ExtendedExpression)
                ));
            }
        }
    }
    println!("actual430rc2 ordinary-Lean binder boundary: closed Many lambda/Pi accepted, closed Zero/One lambda/Pi refused by all candidate-checking routes: PASS");
}

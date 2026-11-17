// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{roots, setup_world};
use super::*;
use clean_kernel::LeanWorld;

#[test]
fn test_replayed_context_435_metadata_qualified_type_and_value_operations() {
    let (_directory, program) = setup_world(LeanWorld::Lean435);
    let context = program
        .replay_context(&roots())
        .expect("qualified435 metadata cone must replay");
    assert!(context.replay_verdict().passed(false));
    assert!(context.replay_verdict().imported_axioms.is_empty());
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let recorded = context.declaration(&Name::from_string("recorded")).unwrap();
    assert!(recorded.is_source_owned());
    context
        .check_expected_type(
            &recorded,
            &[],
            &c("Metadata"),
            ReplayContextLimits::default(),
        )
        .unwrap();
    let target = context
        .declaration(&Name::from_string("targetVal"))
        .unwrap();
    assert!(!target.is_source_owned());
    context
        .check_expected_type(&target, &[], &c("Leaf"), ReplayContextLimits::default())
        .unwrap();
    let binding = context.declaration(&Name::from_string("binding")).unwrap();
    context
        .check_expected_type(
            &binding,
            &[],
            &Expr::apps(c("Holds"), [c("targetVal"), c("targetVal")]),
            ReplayContextLimits::default(),
        )
        .unwrap();
    for (input, answer, expected) in [
        ("Leaf.off", "targetVal", true),
        ("Leaf.on", "Leaf.off", false),
    ] {
        assert_eq!(
            context
                .definitionally_equal(
                    &Expr::app(c("query"), c(input)),
                    &c(answer),
                    ReplayContextLimits::default()
                )
                .unwrap(),
            expected
        );
    }
    let reduced = context
        .whnf_closed(&c("recorded"), ReplayContextLimits::default())
        .unwrap();
    let clean_kernel::ExprKind::Const(constructor_name, _) = reduced.get_app_fn().kind() else {
        panic!("actual record must reduce to its constructor")
    };
    let constructor = context.declaration(constructor_name).unwrap();
    assert_eq!(
        constructor.constructor().unwrap().inductive_name,
        Name::from_string("Metadata")
    );
    println!("actual435 metadata: authenticated actual constructor/import identities, closed expected types and positive/negative defeq: PASS; no query contract or runtime readiness claim");
}

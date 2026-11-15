use super::*;
const INPUT: &str = include_str!("../../tests/fixtures/q2-part2/literals.ndjson");
#[test]
fn target_pins_require_an_accepted_theorem_and_the_exact_statement() {
    let name = Name::from_dotted("q2NatAdd");
    let info = inspect_target(INPUT.as_bytes(), Dialect::Lean4Export31, name.clone()).unwrap();
    assert!(!info.matched);
    assert!(info.axioms.is_empty());
    assert_eq!(info.report.axioms.len(), 3);
    let good = replay_target(
        INPUT.as_bytes(),
        Dialect::Lean4Export31,
        TargetRequest {
            name: name.clone(),
            statement_sha256: info.statement_sha256,
        },
    )
    .unwrap();
    assert!(good.matched);
    for pin in ["0".repeat(64), "F".repeat(64), "abc".into()] {
        let e = replay_target(
            INPUT.as_bytes(),
            Dialect::Lean4Export31,
            TargetRequest {
                name: name.clone(),
                statement_sha256: pin,
            },
        )
        .unwrap_err();
        assert_eq!(e.reason(), "target-policy");
    }
    for name in ["missing", "q2BigNat"] {
        assert_eq!(
            inspect_target(
                INPUT.as_bytes(),
                Dialect::Lean4Export31,
                Name::from_dotted(name)
            )
            .unwrap_err()
            .reason(),
            "target-policy"
        );
    }
}
#[test]
fn target_closure_distinguishes_used_and_unused_allowed_axioms() {
    for (theorem, used) in [
        ("q2ChoiceUse", "Classical.choice"),
        ("q2PropextUse", "propext"),
    ] {
        let result = inspect_target(
            INPUT.as_bytes(),
            Dialect::Lean4Export31,
            Name::from_dotted(theorem),
        )
        .unwrap();
        assert_eq!(result.axioms, vec![Name::from_dotted(used)]);
        assert_eq!(result.report.axioms.len(), 3);
    }
}
#[test]
fn statement_hash_ignores_only_binder_annotations_and_preserves_names() {
    use crate::rawexpr::BinderInfo;
    use crate::{RawExpr, RawLevel};
    let a = RawExpr::Pi(
        BinderInfo::Default,
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    );
    let b = RawExpr::Pi(
        BinderInfo::Implicit,
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    );
    assert_eq!(
        statement::hash(&a, 0).unwrap(),
        statement::hash(&b, 0).unwrap()
    );
    assert_ne!(
        statement::hash(&a, 0).unwrap(),
        statement::hash(&a, 1).unwrap()
    );
    let n = Name::anonymous().str("x");
    let numeric = RawExpr::Const(n.num(1), vec![]);
    let string = RawExpr::Const(n.str("1"), vec![]);
    assert_ne!(
        statement::hash(&numeric, 0).unwrap(),
        statement::hash(&string, 0).unwrap()
    );
    assert_eq!(
        parse_name_components(&name_components(&n.num(u64::MAX))).unwrap(),
        n.num(u64::MAX)
    );
    assert_eq!(
        parse_name_components(&name_components(&n.str("1"))).unwrap(),
        n.str("1")
    );
    // Independently computable binary encoding: domain, arity, Sort tag, Zero.
    assert_eq!(
        statement::hash(&RawExpr::Sort(RawLevel::Zero), 0).unwrap(),
        "0f8f8c1d649bfd5c9313cc1d05a4998df8aa03c23091a2b507a95ad4288681a9"
    );
}

#[test]
fn a_statement_pin_cannot_hide_an_existing_planted_axiom_control() {
    let input = include_str!("../../tests/fixtures/q2-part2/extra-axiom.ndjson");
    let name = Name::from_dotted("q2Eq");
    let info = inspect_target(input.as_bytes(), Dialect::Lean4Export31, name.clone()).unwrap();
    assert!(!info.matched);
    assert_eq!(info.report.counts().1.get("axiom-policy"), Some(&1));
    let result = replay_target(
        input.as_bytes(),
        Dialect::Lean4Export31,
        TargetRequest {
            name,
            statement_sha256: info.statement_sha256,
        },
    )
    .unwrap_err();
    assert_eq!(result.reason(), "target-policy");
    assert!(result
        .to_string()
        .contains("stream contains refused declarations"));
}

/// A checked proposition can have a small DAG and an enormous v1 encoding.
/// Metadata hashing must refuse before streaming its repeated tree paths.
#[test]
fn target_v1_hash_work_is_bounded_after_shared_checking() {
    let mut wire = include_str!("../../tests/fixtures/q2-core.ndjson").to_owned();
    wire.push_str("{\"in\":100,\"str\":{\"pre\":0,\"str\":\"wide_statement\"}}\n");
    let mut previous = 8u64;
    let mut domain = previous;
    for index in 100..124 {
        domain = previous;
        wire.push_str(&format!("{{\"ie\":{index},\"forallE\":{{\"name\":0,\"type\":{previous},\"body\":{previous},\"binderInfo\":\"default\"}}}}\n"));
        previous = index;
    }
    wire.push_str("{\"ie\":200,\"bvar\":0}\n");
    wire.push_str(&format!("{{\"ie\":201,\"lam\":{{\"name\":0,\"type\":{domain},\"body\":200,\"binderInfo\":\"default\"}}}}\n"));
    wire.push_str(&format!("{{\"thm\":{{\"name\":100,\"levelParams\":[],\"type\":{previous},\"value\":201,\"all\":[100]}}}}\n"));
    let report =
        replay(wire.as_bytes(), Dialect::Lean4Export31).expect("the shared theorem is checked");
    assert_eq!(report.counts().0, 3);
    assert!(report.counts().1.is_empty());
    let refused = inspect_target(
        wire.as_bytes(),
        Dialect::Lean4Export31,
        Name::from_dotted("wide_statement"),
    )
    .expect_err("legacy tree-encoded hashing has an independent work envelope");
    assert_eq!(refused.reason(), "resource-limit");
}

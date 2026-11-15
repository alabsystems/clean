use super::*;
use crate::validate::Env;
use crate::{Name, RawExpr};
fn replay_checked(data: &str) -> MinimalEnv {
    let (report, env) = replay_environment(data.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    env
}
#[test]
fn reduced_field_shapes_preserve_declared_types_and_induction_hypotheses() {
    for (data, roots, select) in [
        (
            include_str!("../../tests/fixtures/q2-part2/reduced-field.ndjson"),
            vec![("Q2ReducedField", "mk")],
            "Q2ConstType",
        ),
        (
            include_str!("../../tests/fixtures/q2-part2/reduced-more.ndjson"),
            vec![
                ("Q2ReducedA", "step"),
                ("Q2ReducedB", "step"),
                ("Q2ReducedReflexive", "step"),
            ],
            "Q2ReducedSelect",
        ),
    ] {
        let env = replay_checked(data);
        for (root, constructor) in roots {
            let owner = Name::from_dotted(root);
            let ctor = owner.str(constructor);
            assert!(crate::positivity::term_mentions(
                &env.const_type(&ctor).unwrap(),
                &Name::from_dotted(select)
            ));
            assert!(crate::positivity::term_mentions(
                &env.recursor_type(&owner).unwrap(),
                &Name::from_dotted(select)
            ));
            let rules = env.recursor_rules(&owner).unwrap();
            assert_eq!(
                rules
                    .iter()
                    .find(|r| r.constructor == ctor)
                    .unwrap()
                    .recursive,
                vec![true]
            );
        }
    }
}
#[test]
fn reduced_field_iota_uses_the_independently_derived_recursive_call() {
    let env = replay_checked(include_str!(
        "../../tests/fixtures/q2-part2/reduced-field.ndjson"
    ));
    let c = |n: &str| RawExpr::Const(Name::from_dotted(n), vec![]);
    let app = |f, a| RawExpr::App(Box::new(f), Box::new(a));
    let family = Term::validate(&env, &app(c("Q2ReducedField"), c("Nat")), 0, 0).unwrap();
    let x = RawExpr::BVar(0);
    let fold = app(c("q2ReducedFold"), c("Nat"));
    let major = app(app(c("Q2ReducedField.mk"), c("Nat")), x.clone());
    let left = Term::validate(&env, &app(fold.clone(), major), 1, 0).unwrap();
    let right = Term::validate(&env, &app(c("Nat.succ"), app(fold, x)), 1, 0).unwrap();
    let ctx = [family];
    let view =
        crate::whnf::whnf_in_context(&env, &ctx, &left, &mut Budget::default_budget()).unwrap();
    assert!(
        matches!(view.unfold_apps().0.kind(),crate::term::TermKind::Const(k) if k.name()==&Name::from_dotted("Nat.succ"))
    );
    assert!(crate::def_eq::is_def_eq_in_context(
        &env,
        &ctx,
        &view,
        &right,
        &mut Budget::default_budget()
    )
    .unwrap());
}
#[test]
fn reducing_fields_never_normalizes_the_forbidden_constructor_result() {
    let report = replay(
        include_str!("../../tests/fixtures/q2-part2/arena-056.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    let error = report
        .rows
        .iter()
        .find(|r| r.name == Name::from_dotted("reduceCtorType"))
        .unwrap()
        .verdict
        .as_ref()
        .unwrap_err();
    assert_eq!(error.reason(), "admission");
    assert!(error
        .to_string()
        .contains("generated recursor type failed kernel check"));
}
#[test]
fn shared_mutual_recursion_excludes_field_free_member_from_eta() {
    let env = replay_checked(include_str!(
        "../../tests/fixtures/q2-part2/eta-guard.ndjson"
    ));
    let owner = Name::from_dotted("Q2MixedUnit");
    assert!(env.structure_info(&owner).is_none());
    let family = Term::validate(&env, &RawExpr::Const(owner, vec![]), 0, 0).unwrap();
    let a = Term::validate(&env, &RawExpr::BVar(1), 2, 0).unwrap();
    let b = Term::validate(&env, &RawExpr::BVar(0), 2, 0).unwrap();
    assert!(!crate::def_eq::is_def_eq_in_context(
        &env,
        &[family.clone(), family],
        &a,
        &b,
        &mut Budget::default_budget()
    )
    .unwrap());
}

#[test]
fn raw_annotation_flags_precede_identity_consumption_and_tighten_eta() {
    let env = replay_checked(include_str!(
        "../../tests/fixtures/q2-part2/annotation-flags.ndjson"
    ));
    let rules = env
        .recursor_rules(&Name::from_dotted("Q2AnnotatedField"))
        .unwrap();
    assert_eq!(
        rules
            .iter()
            .find(|r| r.constructor == Name::from_dotted("Q2AnnotatedField.step"))
            .unwrap()
            .recursive,
        vec![true]
    );
    assert!(env
        .structure_info(&Name::from_dotted("Q2AnnotatedEta"))
        .is_none());
}

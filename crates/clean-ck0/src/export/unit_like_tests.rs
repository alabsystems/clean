use super::*;
use crate::{RawExpr, RawLevel};
fn environment() -> MinimalEnv {
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/unit-like.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    env
}
fn ty(env: &MinimalEnv, raw: RawExpr) -> Term {
    Term::validate(env, &raw, 0, 0).unwrap()
}
fn named(name: &str) -> RawExpr {
    RawExpr::Const(Name::from_dotted(name), vec![])
}
fn compare(env: &MinimalEnv, left: Term, right: Term) -> bool {
    let a = Term::validate(env, &RawExpr::BVar(1), 2, 0).unwrap();
    let b = Term::validate(env, &RawExpr::BVar(0), 2, 0).unwrap();
    crate::def_eq::is_def_eq_in_context(env, &[left, right], &a, &b, &mut Budget::default_budget())
        .unwrap()
}
#[test]
fn pinned_neutral_unit_like_values_and_aliases_compare_equal() {
    let env = environment();
    let unit = ty(&env, named("Unit"));
    assert!(compare(&env, unit.clone(), unit));
    let punit = ty(
        &env,
        RawExpr::Const(
            Name::from_dotted("PUnit"),
            vec![RawLevel::Succ(Box::new(RawLevel::Zero))],
        ),
    );
    assert!(compare(&env, punit.clone(), punit));
}
#[test]
fn unit_like_equality_checks_owner_parameters_and_universes() {
    let env = environment();
    let param = |level, argument| {
        ty(
            &env,
            RawExpr::App(
                Box::new(RawExpr::Const(
                    Name::from_dotted("Q2ParamUnit"),
                    vec![level],
                )),
                Box::new(argument),
            ),
        )
    };
    let one = RawLevel::Succ(Box::new(RawLevel::Zero));
    let two = RawLevel::Succ(Box::new(one.clone()));
    let a = param(one.clone(), named("Nat"));
    assert!(compare(&env, a.clone(), a.clone()));
    assert!(!compare(&env, a.clone(), param(one, named("Empty"))));
    assert!(!compare(&env, a.clone(), ty(&env, named("Unit"))));
    let high = param(
        two.clone(),
        RawExpr::Const(Name::from_dotted("PUnit"), vec![two]),
    );
    assert!(!compare(&env, a, high));
}
#[test]
fn fields_and_empty_datatypes_do_not_gain_unit_like_equality() {
    let env = environment();
    for name in ["Q2DataBox", "Empty", "Nat"] {
        let t = ty(&env, named(name));
        assert!(!compare(&env, t.clone(), t), "{name}");
    }
}

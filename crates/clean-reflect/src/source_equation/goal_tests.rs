// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source(environment: &mut Environment, connective: &str) -> Name {
    let name = Name::from_string("OriginalConjunction");
    environment
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop())),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::apps(Expr::const_str(connective), [Expr::bvar(1), Expr::bvar(0)]),
                ),
            ),
            is_reducible: true,
        })
        .expect("original definition fully checked");
    name
}

#[test]
fn original_source_relation_replays_only_against_complete_expected_inputs() {
    let mut environment = Environment::with_prelude();
    let original = source(&mut environment, "And");
    let parameters = [Expr::prop(), Expr::prop()];
    let arguments = [Expr::bvar(1), Expr::bvar(0)];
    let goal = Expr::apps(Expr::const_str("And"), arguments.clone());
    let checked = check_source_goal_relation(
        &environment,
        &original,
        &parameters,
        &arguments,
        &goal,
        Name::from_string("originalRelation"),
    )
    .expect("complete source-to-actual-goal relation");
    let Declaration::Theorem { value, .. } = checked.declaration() else {
        panic!("checked relation is a theorem")
    };
    let replay = |env: &Environment, args: &[Expr], expected: &Expr| {
        check_source_goal_relation_with_proof(
            env,
            &original,
            &parameters,
            args,
            expected,
            Name::from_string("replayedRelation"),
            value.clone(),
        )
    };
    replay(&environment, &arguments, &goal).expect("independent exact replay");
    assert!(
        replay(&environment, &arguments, &Expr::bvar(1)).is_err(),
        "a dropped conjunct must not gain authority"
    );
    assert!(
        replay(&environment, &[Expr::bvar(0), Expr::bvar(1)], &goal).is_err(),
        "operand identity/order must remain bound"
    );
    let mut changed = Environment::with_prelude();
    source(&mut changed, "Or");
    assert!(
        replay(&changed, &arguments, &goal).is_err(),
        "same-named source with a different body must not replay"
    );
    assert!(
        check_source_goal_relation(
            &environment,
            &original,
            &parameters,
            &arguments,
            &Expr::prop(),
            Name::from_string("illTypedGoal"),
        )
        .is_err(),
        "the actual goal must be a proposition, not its sort"
    );
}

#[test]
fn source_relation_refuses_opaque_sources_and_escaped_inputs() {
    let mut environment = Environment::with_prelude();
    let original = source(&mut environment, "And");
    let parameters = [Expr::prop(), Expr::prop()];
    let goal = Expr::apps(Expr::const_str("And"), [Expr::bvar(1), Expr::bvar(0)]);
    assert!(check_source_goal_relation(
        &environment,
        &original,
        &parameters,
        &[Expr::bvar(2), Expr::bvar(0)],
        &goal,
        Name::from_string("escapedInput"),
    )
    .is_err());
    assert!(check_source_goal_relation(
        &environment,
        &Name::from_string("absentOriginal"),
        &parameters,
        &[Expr::bvar(1), Expr::bvar(0)],
        &goal,
        Name::from_string("absentSourceRelation"),
    )
    .is_err());
    let opaque = Name::from_string("OpaqueOriginal");
    let definition = environment
        .get_const(&original)
        .expect("original definition");
    environment
        .add_decl(Declaration::Opaque {
            name: opaque.clone(),
            level_params: vec![],
            type_: definition.type_.clone(),
            value: definition.value.clone().expect("original body"),
        })
        .expect("well-typed opaque constant");
    assert!(
        check_source_goal_relation(
            &environment,
            &opaque,
            &parameters,
            &[Expr::bvar(1), Expr::bvar(0)],
            &goal,
            Name::from_string("opaqueSourceRelation"),
        )
        .is_err(),
        "an opaque witness must not become source semantics"
    );
}

#[test]
fn supplied_lean_relation_can_prove_more_than_conversion() {
    let mut environment = Environment::with_prelude();
    let original = source(&mut environment, "And");
    let parameters = [Expr::prop()];
    let arguments = [Expr::const_str("True"), Expr::bvar(0)];
    let goal = Expr::bvar(0);
    assert!(check_source_goal_relation(
        &environment,
        &original,
        &parameters,
        &arguments,
        &goal,
        Name::from_string("conversionCannotDropTrue")
    )
    .is_err());
    let lhs = Expr::apps(Expr::const_(original.clone(), vec![]), arguments.clone());
    let forward = Expr::lam(
        BinderInfo::Default,
        lhs.clone(),
        Expr::apps(
            Expr::const_str("And.right"),
            [Expr::const_str("True"), Expr::bvar(1), Expr::bvar(0)],
        ),
    );
    let backward = Expr::lam(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::apps(
            Expr::const_str("And.intro"),
            [
                Expr::const_str("True"),
                Expr::bvar(1),
                Expr::const_str("True.intro"),
                Expr::bvar(0),
            ],
        ),
    );
    let proof = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::apps(
            Expr::const_str("Iff.intro"),
            [lhs, goal.clone(), forward, backward],
        ),
    );
    check_source_goal_relation_with_proof(
        &environment,
        &original,
        &parameters,
        &arguments,
        &goal,
        Name::from_string("checkedNonConversionRelation"),
        proof,
    )
    .expect("the complete independently expected relation has a checked proof");
}

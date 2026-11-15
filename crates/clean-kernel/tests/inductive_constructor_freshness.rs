// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The model's family-name freshness must also account for constructor names.
//! This uses genuinely admitted declarations, not unchecked metadata fixtures.

use clean_kernel::env::{Declaration, EnvError};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{Environment, Expr, Name, TypeChecker};

fn family(name: &str, constructor: &str) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(name),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(constructor),
                type_: Expr::const_(Name::from_string(name), vec![]),
            }],
        }],
    }
}

fn table_counts(env: &Environment) -> (usize, usize, usize, usize, u64) {
    (
        env.num_constants(),
        env.num_inductives(),
        env.num_constructors(),
        env.num_recursors(),
        env.generation(),
    )
}

fn add(env: &mut Environment, decl: InductiveDecl, core_only: bool) -> Result<(), EnvError> {
    if core_only {
        env.add_inductive_core(decl)
    } else {
        env.add_inductive(decl)
    }
}

#[test]
fn fresh_family_cannot_reuse_an_admitted_constructor_name() {
    let mut env = Environment::new();
    let first_name = Name::from_string("FirstFreshFamily");
    let constructor = Name::from_string("sharedConstructor");
    let constructor_expr = Expr::const_(constructor.clone(), vec![]);
    env.add_inductive(family("FirstFreshFamily", "sharedConstructor"))
        .expect("the original family and constructor must really be admitted");
    assert_eq!(
        TypeChecker::new(&env)
            .infer_type_full(&constructor_expr)
            .expect("the original constructor must fully type-check"),
        Expr::const_(first_name.clone(), vec![])
    );
    let before = table_counts(&env);
    let original = env
        .get_constructor(&constructor)
        .expect("admission must store actual constructor metadata")
        .clone();

    // The new family is absent, so the already-present-family idempotence
    // branch cannot explain either success or refusal of this declaration.
    let second_name = Name::from_string("SecondFreshFamily");
    assert!(env.get_const(&second_name).is_none());
    assert!(env.get_inductive(&second_name).is_none());
    let error = env
        .add_inductive(family("SecondFreshFamily", "sharedConstructor"))
        .expect_err("fresh family name does not make its constructor name fresh");
    assert!(
        matches!(error, EnvError::DuplicateName(ref name) if name == &constructor),
        "expected the actual constructor collision, got {error:?}"
    );
    assert_eq!(table_counts(&env), before);
    assert!(env.get_const(&second_name).is_none());
    assert!(env.get_inductive(&second_name).is_none());
    assert!(env
        .get_recursor(&Name::from_string("SecondFreshFamily.rec"))
        .is_none());
    let retained = env
        .get_constructor(&constructor)
        .expect("the rejected extension must retain the original constructor");
    assert_eq!(retained.inductive_name, first_name);
    assert_eq!(retained.type_, original.type_);
    assert_eq!(retained.level_params, original.level_params);
    assert_eq!(retained.num_params, original.num_params);
    assert_eq!(retained.num_fields, original.num_fields);
    assert_eq!(retained.constructor_idx, original.constructor_idx);
    assert_eq!(
        TypeChecker::new(&env)
            .infer_type_full(&constructor_expr)
            .expect("the old constructor remains valid after refusal"),
        original.type_
    );

    // Same valid family telescope, genuinely fresh constructor: refusal must
    // not be a blanket ban on extending the already populated environment.
    env.add_inductive(family("SecondFreshFamily", "freshConstructor"))
        .expect("the fresh extension remains accepted after the failed attempt");
    assert_eq!(
        TypeChecker::new(&env)
            .infer_type_full(&Expr::const_(Name::from_string("freshConstructor"), vec![]))
            .expect("the positive-control constructor must fully type-check"),
        Expr::const_(second_name, vec![])
    );
}

#[test]
fn checked_constant_extensions_cannot_reuse_constructor_names() {
    for opaque in [false, true] {
        let mut env = Environment::new();
        env.add_inductive(family("ConstantCollisionFamily", "occupiedConstructor"))
            .expect("admit a real constructor before trying the constant extension");
        let before = table_counts(&env);
        let occupied = Name::from_string("occupiedConstructor");
        let declaration = |name: Name| {
            if opaque {
                Declaration::Opaque {
                    name,
                    level_params: vec![],
                    type_: Expr::type_(),
                    value: Expr::prop(),
                }
            } else {
                Declaration::Definition {
                    name,
                    level_params: vec![],
                    type_: Expr::type_(),
                    value: Expr::prop(),
                    is_reducible: true,
                }
            }
        };
        TypeChecker::new(&env)
            .check_type(&Expr::prop(), &Expr::type_())
            .expect("the attempted constant payload is independently well typed");
        let error = env
            .add_decl(declaration(occupied.clone()))
            .expect_err("a constructor already occupies this constant name");
        assert!(
            matches!(error, EnvError::DuplicateName(ref name) if name == &occupied),
            "opaque={opaque}: expected the actual name collision, got {error:?}"
        );
        assert_eq!(table_counts(&env), before);
        assert_eq!(
            env.get_constructor(&occupied)
                .expect("the original constructor metadata must survive")
                .inductive_name,
            Name::from_string("ConstantCollisionFamily")
        );
        assert_eq!(
            TypeChecker::new(&env)
                .infer_type_full(&Expr::const_(occupied, vec![]))
                .expect("the occupied constant remains the original constructor"),
            Expr::const_(Name::from_string("ConstantCollisionFamily"), vec![])
        );
        env.add_decl(declaration(Name::from_string("genuinelyFreshConstant")))
            .expect("the identical well-typed payload under a fresh name must succeed");
    }
}

#[test]
fn a_constructor_cannot_reuse_its_own_family_name() {
    for core_only in [false, true] {
        let mut env = Environment::new();
        let before = table_counts(&env);
        let error = add(
            &mut env,
            family("SelfCollision", "SelfCollision"),
            core_only,
        )
        .expect_err("family/constructor name collision must return an error, not panic");
        assert!(
            matches!(error, EnvError::DuplicateName(ref name) if name == &Name::from_string("SelfCollision")),
            "core_only={core_only}: expected the actual name collision, got {error:?}"
        );
        assert_eq!(table_counts(&env), before);
        assert!(env.get_const(&Name::from_string("SelfCollision")).is_none());
        add(
            &mut env,
            family("SelfCollision", "SelfCollision.mk"),
            core_only,
        )
        .expect("the same family with a distinct constructor remains admissible");
        assert_eq!(
            TypeChecker::new(&env)
                .infer_type_full(&Expr::const_(Name::from_string("SelfCollision.mk"), vec![]))
                .expect("the positive-control constructor must fully type-check"),
            Expr::const_(Name::from_string("SelfCollision"), vec![])
        );
    }
}

#[test]
fn constructor_names_are_distinct_within_a_new_family() {
    for core_only in [false, true] {
        let mut env = Environment::new();
        let before = table_counts(&env);
        let mut duplicate = family("PairCollision", "PairCollision.first");
        let repeated = duplicate.types[0].constructors[0].clone();
        duplicate.types[0].constructors.push(repeated);
        let error = add(&mut env, duplicate.clone(), core_only)
            .expect_err("two new constructors cannot share one name");
        assert!(
            matches!(error, EnvError::DuplicateName(ref name) if name == &Name::from_string("PairCollision.first")),
            "core_only={core_only}: expected the actual name collision, got {error:?}"
        );
        assert_eq!(table_counts(&env), before);
        assert!(env.get_const(&Name::from_string("PairCollision")).is_none());
        duplicate.types[0].constructors[1].name = Name::from_string("PairCollision.second");
        add(&mut env, duplicate, core_only)
            .expect("the same two-constructor family with distinct names must succeed");
        for (idx, name) in ["PairCollision.first", "PairCollision.second"]
            .into_iter()
            .enumerate()
        {
            let name = Name::from_string(name);
            assert_eq!(
                env.get_constructor(&name)
                    .expect("each constructor keeps its own metadata")
                    .constructor_idx as usize,
                idx
            );
            assert_eq!(
                TypeChecker::new(&env)
                    .infer_type_full(&Expr::const_(name, vec![]))
                    .expect("both positive-control constructors must fully type-check"),
                Expr::const_(Name::from_string("PairCollision"), vec![])
            );
        }
    }
}

fn mutual_family() -> InductiveDecl {
    let mut decl = family("MutualLeft", "MutualLeft.mk");
    decl.types
        .extend(family("MutualRight", "MutualRight.mk").types);
    decl
}

fn assert_mutual_refusal_then_positive(decl: InductiveDecl, collision: &str) {
    for core_only in [false, true] {
        for reversed in [false, true] {
            let mut env = Environment::new();
            env.add_inductive(family("RetainedFamily", "RetainedFamily.mk"))
                .expect("retain an actually admitted declaration across refusal");
            let before = table_counts(&env);
            let mut input = decl.clone();
            if reversed {
                input.types.reverse();
            }
            let error = add(&mut env, input, core_only)
                .expect_err("mutual block names must be distinct before staging any member");
            assert!(
                matches!(error, EnvError::DuplicateName(ref name) if name == &Name::from_string(collision)),
                "core_only={core_only}, reversed={reversed}: got {error:?}"
            );
            assert_eq!(table_counts(&env), before);
            for name in ["MutualLeft", "MutualRight"] {
                assert!(env.get_const(&Name::from_string(name)).is_none());
                assert!(env.get_inductive(&Name::from_string(name)).is_none());
            }
            add(&mut env, mutual_family(), core_only)
                .expect("the distinct-name mutual positive control must still succeed");
            for (ctor, owner) in [
                ("RetainedFamily.mk", "RetainedFamily"),
                ("MutualLeft.mk", "MutualLeft"),
                ("MutualRight.mk", "MutualRight"),
            ] {
                assert_eq!(
                    TypeChecker::new(&env)
                        .infer_type_full(&Expr::const_(Name::from_string(ctor), vec![]))
                        .expect("old and new constructors remain fully typed"),
                    Expr::const_(Name::from_string(owner), vec![])
                );
            }
        }
    }
}

#[test]
fn mutual_family_names_are_distinct() {
    let mut decl = mutual_family();
    decl.types[1].name = Name::from_string("MutualLeft");
    decl.types[1].constructors[0].type_ = Expr::const_(Name::from_string("MutualLeft"), vec![]);
    assert_mutual_refusal_then_positive(decl, "MutualLeft");
}

#[test]
fn constructor_names_cannot_overlap_a_sibling_family() {
    let mut decl = mutual_family();
    decl.types[0].constructors[0].name = Name::from_string("MutualRight");
    assert_mutual_refusal_then_positive(decl, "MutualRight");
}

#[test]
fn constructor_names_are_distinct_across_mutual_families() {
    let mut decl = mutual_family();
    decl.types[1].constructors[0].name = Name::from_string("MutualLeft.mk");
    assert_mutual_refusal_then_positive(decl, "MutualLeft.mk");
}

#[test]
fn genuine_reregistration_is_unchanged_but_duplicate_payload_is_refused() {
    for core_only in [false, true] {
        let mut env = Environment::new();
        let decl = mutual_family();
        add(&mut env, decl.clone(), core_only).expect("the mutual family must really be admitted");
        let before = table_counts(&env);
        add(&mut env, decl.clone(), core_only)
            .expect("genuine re-registration keeps its existing successful no-op behavior");
        assert_eq!(table_counts(&env), before);
        let mut duplicate = decl;
        let repeated = duplicate.types[0].constructors[0].clone();
        duplicate.types[0].constructors.push(repeated);
        let error = add(&mut env, duplicate, core_only)
            .expect_err("all names being present must not bypass intra-block uniqueness");
        assert!(
            matches!(error, EnvError::DuplicateName(ref name) if name == &Name::from_string("MutualLeft.mk")),
            "core_only={core_only}: got {error:?}"
        );
        assert_eq!(table_counts(&env), before);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Generated names must preserve Name constructors, not their dotted display.
use clean_kernel::env::{
    ContainerMapOutcome, ContainerRelOutcome, DeclarationVerification, DeepIndOutcome,
};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

fn constant(name: &Name) -> Expr {
    Expr::const_(name.clone(), vec![])
}
fn counter(name: &Name) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name.clone().str("zero"),
                    type_: constant(name),
                },
                Constructor {
                    name: name.clone().str("next"),
                    type_: Expr::arrow(constant(name), constant(name)),
                },
            ],
        }],
    }
}
fn typed_names() -> Vec<Name> {
    vec![
        Name::from_string("Plain.Family"),
        Name::anon().str("Quoted.Family"),
        Name::anon().str("数字.型"),
        Name::anon().str("Generated").num(7),
        Name::anon().str("Generated").str("7"),
    ]
}
fn checked_values(env: &Environment, parent: &Name, suffixes: &[&str]) {
    let tc = TypeChecker::new(env);
    for suffix in suffixes {
        let name = parent.clone().str(suffix);
        let info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("missing {name:?}"));
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
        if let Some(value) = &info.value {
            let inferred = tc
                .infer_type(value)
                .unwrap_or_else(|error| panic!("{name:?}: {error}"));
            assert!(tc.is_def_eq(&inferred, &info.type_), "{name:?}");
        }
    }
}

#[test]
fn core_distinguishes_quoted_dots_and_numeric_string_components() {
    let mut env = Environment::default();
    let names = typed_names();
    for name in &names {
        env.add_inductive_core(counter(name)).unwrap();
    }
    assert_eq!(env.constants().count(), names.len() * 4);
    for name in names {
        checked_values(&env, &name, &["rec"]);
    }
}

#[test]
fn core_recursive_iota_uses_exact_typed_recursor_identity() {
    for name in typed_names() {
        let mut env = Environment::default();
        env.add_inductive_core(counter(&name)).unwrap();
        let ty = constant(&name);
        let zero = constant(&name.clone().str("zero"));
        let next = constant(&name.clone().str("next"));
        let motive = Expr::lam(BinderInfo::Default, ty.clone(), ty.clone());
        let step = Expr::lam(
            BinderInfo::Default,
            ty.clone(),
            Expr::lam(
                BinderInfo::Default,
                ty,
                Expr::app(next.clone(), Expr::bvar(0)),
            ),
        );
        let value = Expr::app(next, zero.clone());
        let rec = Expr::const_(name.clone().str("rec"), vec![Level::succ(Level::zero())]);
        let applied = Expr::app(
            Expr::app(Expr::app(Expr::app(rec, motive), zero), step),
            value.clone(),
        );
        let tc = TypeChecker::new(&env);
        assert!(tc.is_def_eq(&tc.infer_type(&applied).unwrap(), &constant(&name)));
        assert!(tc.is_def_eq(&applied, &value), "{name:?}");
    }
}

#[test]
fn full_generated_eliminators_and_no_confusion_preserve_parent() {
    for name in typed_names() {
        let mut env = Environment::with_prelude();
        env.add_inductive(counter(&name)).unwrap();
        checked_values(
            &env,
            &name,
            &["rec", "casesOn", "recOn", "noConfusionType", "noConfusion"],
        );
    }
}

#[test]
fn full_display_aliases_coexist_without_cross_family_generated_values() {
    let mut env = Environment::with_prelude();
    let names = typed_names();
    for name in &names {
        env.add_inductive(counter(name)).unwrap();
    }
    for name in names {
        checked_values(
            &env,
            &name,
            &["rec", "casesOn", "recOn", "noConfusionType", "noConfusion"],
        );
        assert_eq!(
            env.get_recursor(&name.clone().str("rec"))
                .unwrap()
                .inductive_name,
            name
        );
    }
}

#[test]
fn mutual_display_aliases_keep_their_own_recursor_rules() {
    let names = [
        Name::anon().str("Mutual.Family"),
        Name::from_string("Mutual.Family"),
    ];
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: names
            .iter()
            .enumerate()
            .map(|(index, name)| InductiveType {
                name: name.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: name.clone().str("zero"),
                        type_: constant(name),
                    },
                    Constructor {
                        name: name.clone().str("next"),
                        type_: Expr::arrow(constant(&names[1 - index]), constant(name)),
                    },
                ],
            })
            .collect(),
    };
    let mut env = Environment::default();
    env.add_inductive_core(decl).unwrap();
    assert_eq!(env.constants().count(), 8);
    for name in &names {
        checked_values(&env, name, &["rec"]);
        let rec = env.get_recursor(&name.clone().str("rec")).unwrap();
        assert_eq!(rec.inductive_name, *name);
        assert_eq!(env.get_inductive(name).unwrap().all_names, names);
        assert_eq!(rec.num_motives, 2);
        assert_eq!(rec.rules.len(), 2);
        assert_eq!(
            rec.rules
                .iter()
                .map(|rule| rule.constructor_name.clone())
                .collect::<Vec<_>>(),
            vec![name.clone().str("zero"), name.clone().str("next")]
        );
    }
}

#[test]
fn recursive_below_and_brec_on_preserve_parent() {
    for name in typed_names() {
        let mut env = Environment::default();
        env.init_eq().unwrap();
        env.init_punit().unwrap();
        env.init_pprod().unwrap();
        env.add_inductive(counter(&name)).unwrap();
        checked_values(&env, &name, &["below", "brecOn"]);
    }
}

fn container(name: &Name, constructors: &[Name]) -> InductiveDecl {
    let result = Expr::app(constant(name), Expr::bvar(1));
    let ctor_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::arrow(Expr::bvar(0), result),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
            constructors: constructors
                .iter()
                .map(|name| Constructor {
                    name: name.clone(),
                    type_: ctor_ty.clone(),
                })
                .collect(),
        }],
    }
}

#[test]
fn container_map_preserves_typed_parent_and_checked_value() {
    for name in typed_names() {
        let mut env = Environment::default();
        env.add_inductive_core(container(&name, &[name.clone().str("mk")]))
            .unwrap();
        let ContainerMapOutcome::Decls { definitions } =
            env.synthesize_container_map(&name).unwrap()
        else {
            panic!("map refused {name:?}");
        };
        assert_eq!(definitions.len(), 1);
        for definition in definitions {
            env.add_decl(definition).unwrap();
        }
        checked_values(&env, &name, &["map"]);
    }
}

#[test]
fn relational_constructor_suffixes_keep_dots_and_numeric_kind() {
    // All three suffixes are distinct even when their printed spellings collide.
    let name = Name::anon().str("Container.Family");
    let constructors = [
        name.clone().str("quoted.ctor"),
        name.clone().str("7"),
        name.clone().num(7),
    ];
    let mut env = Environment::default();
    env.add_inductive_core(container(&name, &constructors))
        .unwrap();
    let ContainerRelOutcome::Decls { families } = env.synthesize_container_rel(&name).unwrap()
    else {
        panic!("rel refused");
    };
    assert_eq!(families.len(), 1);
    let relation = name.clone().str("rel");
    let family = &families[0].types[0];
    assert_eq!(family.name, relation);
    assert_eq!(
        family
            .constructors
            .iter()
            .map(|ctor| ctor.name.clone())
            .collect::<Vec<_>>(),
        vec![
            relation.clone().str("quoted.ctor"),
            relation.clone().str("7"),
            relation.clone().num(7)
        ]
    );
    for declaration in families {
        env.add_inductive_core(declaration).unwrap();
    }
    assert_eq!(
        env.get_inductive(&relation)
            .unwrap()
            .constructor_names
            .len(),
        3
    );
}

fn nested(name: &Name) -> InductiveDecl {
    let mut decl = counter(name);
    decl.types[0].constructors.push(Constructor {
        name: name.clone().str("children"),
        type_: Expr::arrow(
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                constant(name),
            ),
            constant(name),
        ),
    });
    decl
}

#[test]
fn nested_restore_preserves_quoted_parent_and_companion_names() {
    for name in [
        Name::from_string("PlainNested"),
        Name::anon().str("Nested.Quoted"),
    ] {
        let mut env = Environment::with_prelude();
        env.add_inductive(nested(&name)).unwrap();
        assert!(env.get_inductive(&name).unwrap().is_nested);
        checked_values(
            &env,
            &name,
            &[
                "rec",
                "rec_1",
                "casesOn",
                "recOn",
                "noConfusionType",
                "noConfusion",
            ],
        );
    }
}

#[test]
fn nested_deep_induction_preserves_typed_parent() {
    for name in [
        Name::from_string("PlainDeep"),
        Name::anon().str("Deep.Quoted"),
    ] {
        let mut env = Environment::with_prelude();
        env.add_inductive(nested(&name)).unwrap();
        let DeepIndOutcome::Decls {
            all_families,
            theorems,
        } = env.synthesize_deep_induction(&name).unwrap()
        else {
            panic!("deep induction refused {name:?}");
        };
        for declaration in all_families {
            env.add_inductive(declaration).unwrap();
        }
        for theorem in theorems {
            env.add_decl(theorem).unwrap();
        }
        checked_values(&env, &name, &["deep_ind"]);
    }
}

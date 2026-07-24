// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Authority-boundary regressions for inductive admission and iota rules.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

fn two_ctor_enum(name: &str) -> InductiveDecl {
    let ind_name = Name::from_string(name);
    let ind = Expr::const_(ind_name.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(&format!("{name}.left")),
                    type_: ind.clone(),
                },
                Constructor {
                    name: Name::from_string(&format!("{name}.right")),
                    type_: ind,
                },
            ],
        }],
    }
}

#[derive(Debug, PartialEq, Eq)]
struct FamilyTableShape {
    constants: usize,
    origins: usize,
    verification: usize,
    inductives: usize,
    constructors: usize,
    recursors: usize,
    structure_fields: usize,
    classes: usize,
    instance_classes: usize,
    instance_names: usize,
    param_names: usize,
    param_binder_infos: usize,
    generation: u64,
}

fn family_table_shape(env: &Environment) -> FamilyTableShape {
    FamilyTableShape {
        constants: env.constants.len(),
        origins: env.constant_origins.len(),
        verification: env.declaration_verification.len(),
        inductives: env.inductives.len(),
        constructors: env.constructors.len(),
        recursors: env.recursors.len(),
        structure_fields: env.structure_fields.len(),
        classes: env.classes.len(),
        instance_classes: env.instances.len(),
        instance_names: env.instance_names.len(),
        param_names: env.param_names.len(),
        param_binder_infos: env.param_binder_infos.len(),
        generation: env.generation,
    }
}

fn replace_final_pi_domain(type_: &Expr, replacement: Expr) -> Expr {
    let ExprKind::Pi(binder, domain, codomain) = type_.kind() else {
        panic!("expected a nonempty Pi telescope, got {type_:?}");
    };
    if matches!(codomain.kind(), ExprKind::Pi(..)) {
        Expr::pi(
            *binder,
            domain.as_ref().clone(),
            replace_final_pi_domain(codomain, replacement),
        )
    } else {
        Expr::pi(*binder, replacement, codomain.as_ref().clone())
    }
}

fn assert_recursor_collision_rolls_back(name: &str, core_only: bool) {
    let mut env = Environment::new();
    let rec_name = Name::from_string(&format!("{name}.rec"));
    env.add_decl(Declaration::Axiom {
        name: rec_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("collision fixture should register");

    let tables_before = family_table_shape(&env);
    let verification_before = env.declaration_verification(&rec_name);

    let family_name = Name::from_string(name);
    let ctor_name = Name::from_string(&format!("{name}.left"));
    let declaration = two_ctor_enum(name);
    let result = if core_only {
        env.add_inductive_core(declaration)
    } else {
        env.add_inductive(declaration)
    };
    let error = result.expect_err("occupied generated recursor name must reject the family");
    assert!(matches!(error, EnvError::DuplicateName(name) if name == rec_name));

    assert_eq!(family_table_shape(&env), tables_before);
    assert_eq!(env.declaration_verification(&rec_name), verification_before);
    assert!(env.get_const(&family_name).is_none());
    assert!(env.get_inductive(&family_name).is_none());
    assert!(env.get_const(&ctor_name).is_none());
    assert!(env.get_constructor(&ctor_name).is_none());
    assert!(
        env.get_const(&rec_name).is_some(),
        "collision fixture was lost"
    );
}

#[test]
fn inductive_recursor_name_collision_rolls_back_every_family_table() {
    assert_recursor_collision_rolls_back("AtomicFamily", false);
}

#[test]
fn inductive_core_recursor_name_collision_uses_same_transaction() {
    assert_recursor_collision_rolls_back("AtomicCoreFamily", true);
}

#[test]
fn recursor_full_validation_rejects_duplicate_rule_and_missing_constructor() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Roster"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Roster.rec");
    let left = Name::from_string("Roster.left");
    let rec = env
        .recursors
        .get_mut(&rec_name)
        .expect("generated recursor");
    assert_eq!(rec.rules.len(), 2);
    rec.rules[1].constructor_name = left;
    env.declaration_verification
        .insert(rec_name.clone(), DeclarationVerification::StructuralOnly);

    let error = env
        .validate_and_stamp_recursor(&rec_name)
        .expect_err("duplicate rule key must not earn full authority");
    assert!(format!("{error:?}").contains("duplicate rule"));
    assert_eq!(
        env.declaration_verification(&rec_name),
        Some(DeclarationVerification::StructuralOnly)
    );
}

#[test]
fn recursor_full_validation_rejects_well_formed_wrong_rule_rhs() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Subject"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Subject.rec");
    let rec = env
        .recursors
        .get_mut(&rec_name)
        .expect("generated recursor");
    assert_eq!(rec.rules.len(), 2);

    // Both RHSs have the same closed lambda shape.  Reusing the left rule for
    // the right constructor is therefore syntactically well formed, but returns
    // the left minor (`motive left`) where `motive right` is required.
    rec.rules[1].rhs = rec.rules[0].rhs.clone();
    env.declaration_verification
        .insert(rec_name.clone(), DeclarationVerification::StructuralOnly);

    let error = env
        .validate_and_stamp_recursor(&rec_name)
        .expect_err("wrong-typed reduction payload must not earn full authority");
    assert!(format!("{error:?}").contains("violates subject reduction"));
    assert_eq!(
        env.declaration_verification(&rec_name),
        Some(DeclarationVerification::StructuralOnly)
    );
}

#[test]
fn read_only_recursor_authentication_accepts_canonical_packets() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Canonical"))
        .expect("valid enum should register");

    for suffix in ["rec", "casesOn", "recOn"] {
        let name = Name::from_string(&format!("Canonical.{suffix}"));
        env.authenticate_recursor_readonly(&name)
            .unwrap_or_else(|error| panic!("canonical `{name}` packet must authenticate: {error}"));
    }
}

#[test]
fn read_only_recursor_authentication_rejects_reordered_rules() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Ordered"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Ordered.rec");
    env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor")
        .rules
        .swap(0, 1);

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("constructor rules are positional reduction authority");
    assert!(
        error.contains("canonical declaration order"),
        "reordered rules must report their positional disagreement, got {error}"
    );
}

#[test]
fn read_only_recursor_authentication_rejects_missing_rule() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Missing"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Missing.rec");
    env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor")
        .rules
        .pop();

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("a partial constructor roster must not authenticate");
    assert!(
        error.contains("rules but num_minors") || error.contains("has 2 constructors"),
        "missing rule must report an exact arity disagreement, got {error}"
    );
}

#[test]
fn read_only_recursor_authentication_rejects_overapplied_major_spine() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("MajorSpine"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("MajorSpine.rec");
    let overapplied_major = Expr::app(
        Expr::const_(Name::from_string("MajorSpine"), vec![]),
        Expr::type_(),
    );
    let malformed_type = replace_final_pi_domain(
        &env.get_recursor(&rec_name)
            .expect("generated recursor")
            .type_,
        overapplied_major,
    );
    env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor")
        .type_ = malformed_type.clone();
    env.constants
        .get_mut(&rec_name)
        .expect("generated recursor constant")
        .type_ = malformed_type;

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("an overapplied major premise must not be truncated to its expected prefix");
    assert!(
        error.contains("major premise supplies 1 inductive arguments, expected 0"),
        "overapplied major spine must report its exact arity, got {error}"
    );
}

#[test]
fn read_only_recursor_authentication_rejects_overapplied_constructor_return_spine() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("ReturnSpine"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("ReturnSpine.rec");
    let ctor_name = Name::from_string("ReturnSpine.left");
    let malformed_type = Expr::app(
        Expr::const_(Name::from_string("ReturnSpine"), vec![]),
        Expr::type_(),
    );
    env.constructors
        .get_mut(&ctor_name)
        .expect("generated constructor")
        .type_ = malformed_type.clone();
    env.constants
        .get_mut(&ctor_name)
        .expect("generated constructor constant")
        .type_ = malformed_type;

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("an overapplied constructor return must not expose only an index prefix");
    assert!(
        error.contains("return supplies 1 inductive arguments, expected 0"),
        "overapplied constructor return must report its exact arity, got {error}"
    );
}

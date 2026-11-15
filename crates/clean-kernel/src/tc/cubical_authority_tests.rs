// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verdict-level pins for the cubical/directed reserved-head authority.

use std::collections::HashSet;

use super::{canonical_declarations, cubical_primitives_canonical, reserved_names};
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::mode::CleanMode;
use crate::name::Name;
use crate::tc::reduction::directed::register_directed_axioms;
use crate::tc::reduction::kan::{
    register_glue_axioms, register_kan_system_axioms, register_sigma_axioms,
};

fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}

fn cubical_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("kan system axioms");
    register_glue_axioms(&mut env).expect("glue axioms");
    register_sigma_axioms(&mut env).expect("sigma axioms");
    env
}

/// The table covers every name a rule recognises: a reserved name no registrar
/// installs could never be admitted, and a rule keyed on it would be dead.
#[test]
fn test_every_reserved_name_is_installed_by_a_registrar() {
    let canonical = canonical_declarations().expect("the registrars succeed");
    let missing: Vec<String> = reserved_names()
        .into_iter()
        .filter(|name| !canonical.contains_key(*name))
        .map(ToString::to_string)
        .collect();
    assert!(
        missing.is_empty(),
        "reserved but never installed: {missing:?}"
    );
}

/// The exact-declaration test is closed: a canonical declaration mentions no
/// constant outside the reserved set, so matching the reserved names alone
/// pins every constant the rules' justification depends on.
#[test]
fn test_canonical_declarations_mention_only_reserved_constants() {
    let canonical = canonical_declarations().expect("the registrars succeed");
    let reserved: HashSet<Name> = reserved_names().into_iter().cloned().collect();
    let mut outside = Vec::new();
    for (name, info) in &canonical {
        let mut mentioned = info.type_.collect_constants();
        if let Some(value) = &info.value {
            value.collect_constants_into(&mut mentioned);
        }
        outside.extend(
            mentioned
                .into_iter()
                .filter(|c| !reserved.contains(c))
                .map(|c| format!("{name} mentions {c}")),
        );
    }
    assert!(outside.is_empty(), "{outside:?}");
}

#[test]
fn test_registrar_environments_are_admitted() {
    assert!(cubical_primitives_canonical(&cubical_env()));
    let mut directed = Environment::with_mode(CleanMode::Directed);
    register_directed_axioms(&mut directed).expect("directed axioms");
    register_kan_system_axioms(&mut directed).expect("kan system axioms");
    register_glue_axioms(&mut directed).expect("glue axioms");
    assert!(cubical_primitives_canonical(&directed));
}

/// No reserved name declared: nothing a rule could match, nothing to refuse.
#[test]
fn test_environment_without_reserved_names_is_admitted() {
    assert!(cubical_primitives_canonical(&Environment::with_mode(
        CleanMode::Cubical
    )));
}

#[test]
fn test_user_redeclaration_is_refused() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("I.neg"),
        level_params: vec![],
        type_: Expr::arrow(interval(), interval()),
        value: Expr::lam(BinderInfo::Default, interval(), Expr::bvar(0)),
        is_reducible: true,
    })
    .expect("user I.neg");
    assert!(!cubical_primitives_canonical(&env));
}

/// Content, not provenance: a user axiom written exactly as the registrar
/// writes it IS the primitive, so it is admitted.
#[test]
fn test_exact_copy_of_a_primitive_is_admitted() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("I.neg"),
        level_params: vec![],
        type_: Expr::arrow(interval(), interval()),
    })
    .expect("user I.neg axiom");
    assert!(cubical_primitives_canonical(&env));
}

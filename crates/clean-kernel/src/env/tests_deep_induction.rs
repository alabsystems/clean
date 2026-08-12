// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for deep-induction synthesis (`inductive_deep_induction.rs`,
//! rung P4). Acceptance = the generated All family passes checked
//! `add_inductive` AND the generated theorem passes checked `add_decl` —
//! the kernel referees the proof term.

use super::inductive_deep_induction::DeepIndOutcome;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

fn sort_u(u: &Name) -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))))
}

/// `MyList.{u} : Type u → Type u | nil | cons : A → MyList A → MyList A`
fn add_mylist(env: &mut Environment) {
    let u = Name::from_string("u");
    let list_at = |a: Expr| {
        Expr::app(
            Expr::const_(Name::from_string("MyList"), vec![Level::param(u.clone())]),
            a,
        )
    };
    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("MyList"),
            type_: Expr::pi(BinderInfo::Default, sort_u(&u), sort_u(&u)),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyList.nil"),
                    type_: Expr::pi(BinderInfo::Implicit, sort_u(&u), list_at(Expr::bvar(0))),
                },
                Constructor {
                    name: Name::from_string("MyList.cons"),
                    type_: Expr::pi(
                        BinderInfo::Implicit,
                        sort_u(&u),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(0),
                            Expr::pi(
                                BinderInfo::Default,
                                list_at(Expr::bvar(1)),
                                list_at(Expr::bvar(2)),
                            ),
                        ),
                    ),
                },
            ],
        }],
    })
    .expect("MyList registers");
}

/// `Term : Type | app : MyList Term → Term` — the post's nested shape.
fn add_term(env: &mut Environment) {
    let term = Expr::const_(Name::from_string("Term"), vec![]);
    let list_term = Expr::app(
        Expr::const_(Name::from_string("MyList"), vec![Level::zero()]),
        term.clone(),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Term"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Term.app"),
                type_: Expr::pi(BinderInfo::Default, list_term, term),
            }],
        }],
    })
    .expect("nested Term registers");
}

fn init_true(env: &mut Environment) {
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("True"),
            type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
            constructors: vec![Constructor {
                name: Name::from_string("True.intro"),
                type_: Expr::const_(Name::from_string("True"), vec![]),
            }],
        }],
    })
    .expect("True registers");
}

#[test]
fn test_deep_induction_term_list_lands_and_kernel_checks() {
    let mut env = Environment::new();
    init_true(&mut env);
    add_mylist(&mut env);
    add_term(&mut env);
    let tv = env
        .get_inductive(&Name::from_string("Term"))
        .expect("Term present");
    assert!(tv.is_nested, "fixture premise: Term is nested");

    let outcome = env
        .synthesize_deep_induction(&Name::from_string("Term"))
        .expect("synthesis must not hit an invariant failure");
    let DeepIndOutcome::Decls {
        all_families,
        theorems,
    } = outcome
    else {
        panic!("Term/MyList must be in the v1 class");
    };
    assert_eq!(all_families.len(), 1, "MyList.All is fresh");
    assert_eq!(theorems.len(), 1, "one deep_ind theorem");
    for fam in all_families {
        env.add_inductive(fam)
            .expect("MyList.All must pass the full kernel check");
    }
    for thm in theorems {
        let name = match &thm {
            Declaration::Theorem { name, .. } => name.clone(),
            other => panic!("deep_ind must be a Theorem, got {other:?}"),
        };
        env.add_decl(thm)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e}"));
    }
    let deep = env
        .get_const(&Name::from_string("Term.deep_ind"))
        .expect("Term.deep_ind registered");
    assert!(
        crate::inductive::mentions_name(&deep.type_, &Name::from_string("MyList.All")),
        "the statement must speak the elementwise All vocabulary"
    );
    assert!(
        !format!("{:?}", deep.type_).contains("_nested"),
        "no internal machinery names in the statement"
    );
}

#[test]
fn test_deep_induction_declines_non_nested() {
    let mut env = Environment::new();
    init_true(&mut env);
    add_mylist(&mut env);
    let outcome = env
        .synthesize_deep_induction(&Name::from_string("MyList"))
        .expect("declining is not an error");
    assert!(
        matches!(outcome, DeepIndOutcome::OutOfScope { .. }),
        "a plain (non-nested) inductive must decline"
    );
}

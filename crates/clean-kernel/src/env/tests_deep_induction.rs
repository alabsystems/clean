// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the rung-P4 generic per-container families:
//! deep-induction synthesis (`inductive_deep_induction.rs`) and the
//! functorial container map (`inductive_container_map.rs`). Acceptance =
//! the generated All family passes checked `add_inductive`, the generated
//! theorem and `C.map` definition pass checked `add_decl` — the kernel
//! referees every term — and `C.map` actually COMPUTES on constructors.

use super::inductive_container_map::ContainerMapOutcome;
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

// ── `C.map` fixtures ──────────────────────────────────────────────────────

/// `MyTree.{u} : Type u → Type u | leaf : A → MyTree A
///                               | node : MyTree A → MyTree A → MyTree A`
///
/// The `node` constructor is the one that matters: TWO self-recursive
/// fields, so the two induction hypotheses share the type `MyTree B` and
/// cannot be told apart by type alone.
fn add_mytree(env: &mut Environment) {
    let u = Name::from_string("u");
    let tree_at = |a: Expr| {
        Expr::app(
            Expr::const_(Name::from_string("MyTree"), vec![Level::param(u.clone())]),
            a,
        )
    };
    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("MyTree"),
            type_: Expr::pi(BinderInfo::Default, sort_u(&u), sort_u(&u)),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyTree.leaf"),
                    type_: Expr::pi(
                        BinderInfo::Implicit,
                        sort_u(&u),
                        Expr::pi(BinderInfo::Default, Expr::bvar(0), tree_at(Expr::bvar(1))),
                    ),
                },
                Constructor {
                    name: Name::from_string("MyTree.node"),
                    type_: Expr::pi(
                        BinderInfo::Implicit,
                        sort_u(&u),
                        Expr::pi(
                            BinderInfo::Default,
                            tree_at(Expr::bvar(0)),
                            Expr::pi(
                                BinderInfo::Default,
                                tree_at(Expr::bvar(1)),
                                tree_at(Expr::bvar(2)),
                            ),
                        ),
                    ),
                },
            ],
        }],
    })
    .expect("MyTree registers");
}

/// `Two : Type | t0 | t1` — two distinguishable closed elements.
fn add_two(env: &mut Environment) {
    let two = Expr::const_(Name::from_string("Two"), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Two"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Two.t0"),
                    type_: two.clone(),
                },
                Constructor {
                    name: Name::from_string("Two.t1"),
                    type_: two,
                },
            ],
        }],
    })
    .expect("Two registers");
}

fn two() -> Expr {
    Expr::const_(Name::from_string("Two"), vec![])
}

fn t(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

/// Register `C.map` through the CHECKED `add_decl` path.
fn register_map(env: &mut Environment, container: &str) {
    let outcome = env
        .synthesize_container_map(&Name::from_string(container))
        .expect("synthesis must not hit an invariant failure");
    let ContainerMapOutcome::Decls { definitions } = outcome else {
        panic!("{container} must be in the v1 container class");
    };
    assert_eq!(definitions.len(), 1, "one {container}.map definition");
    for def in definitions {
        let name = match &def {
            Declaration::Definition { name, .. } => name.clone(),
            other => panic!("{container}.map must be a Definition, got {other:?}"),
        };
        env.add_decl(def)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e}"));
    }
}

#[test]
fn test_container_map_list_kernel_checks_and_computes() {
    let mut env = Environment::new();
    add_mylist(&mut env);
    add_two(&mut env);
    register_map(&mut env, "MyList");

    let map = env
        .get_const(&Name::from_string("MyList.map"))
        .expect("MyList.map registered");
    assert_eq!(
        map.level_params,
        vec![Name::from_string("u")],
        "MyList.map carries MyList's own level params"
    );

    // `f := λ _ : Two. Two.t1` — a NON-identity transport, so a map that
    // silently dropped `f` would not reach the expected value.
    let f = Expr::lam(BinderInfo::Default, two(), t("Two.t1"));
    let nil = Expr::app(
        Expr::const_(Name::from_string("MyList.nil"), vec![Level::zero()]),
        two(),
    );
    let cons = |hd: Expr, tl: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("MyList.cons"), vec![Level::zero()]),
            [two(), hd, tl],
        )
    };
    let input = cons(t("Two.t0"), cons(t("Two.t0"), nil.clone()));
    let mapped = Expr::apps(
        Expr::const_(Name::from_string("MyList.map"), vec![Level::zero()]),
        [two(), two(), f, input.clone()],
    );
    let expected = cons(t("Two.t1"), cons(t("Two.t1"), nil));

    let tc = crate::tc::TypeChecker::new(&env);
    let ty = tc
        .infer_type(&mapped)
        .expect("the mapped list must type-check");
    assert!(
        tc.is_def_eq(
            &ty,
            &Expr::app(
                Expr::const_(Name::from_string("MyList"), vec![Level::zero()]),
                two()
            )
        ),
        "MyList.map lands in the TARGET container type; got {ty:?}"
    );
    assert!(
        tc.is_def_eq(&mapped, &expected),
        "MyList.map must iota-reduce elementwise through f; got {:?}",
        tc.whnf(&mapped)
    );
    assert!(
        !tc.is_def_eq(&mapped, &input),
        "a map that ignored f would leave the input unchanged"
    );
}

#[test]
fn test_container_map_tree_keeps_recursive_field_order() {
    // The IH-order regression guard: `node` has two same-typed IHs, so a
    // synthesizer that paired them with the wrong fields would still be
    // well-typed. Mapping the IDENTITY over an asymmetric tree pins it.
    let mut env = Environment::new();
    add_mytree(&mut env);
    add_two(&mut env);
    register_map(&mut env, "MyTree");

    let leaf = |x: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("MyTree.leaf"), vec![Level::zero()]),
            [two(), x],
        )
    };
    let node = |l: Expr, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("MyTree.node"), vec![Level::zero()]),
            [two(), l, r],
        )
    };
    let id = Expr::lam(BinderInfo::Default, two(), Expr::bvar(0));
    let input = node(leaf(t("Two.t0")), leaf(t("Two.t1")));
    let swapped = node(leaf(t("Two.t1")), leaf(t("Two.t0")));
    let mapped = Expr::apps(
        Expr::const_(Name::from_string("MyTree.map"), vec![Level::zero()]),
        [two(), two(), id, input.clone()],
    );

    let tc = crate::tc::TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&mapped, &input),
        "mapping the identity must return the tree unchanged; got {:?}",
        tc.whnf(&mapped)
    );
    assert!(
        !tc.is_def_eq(&mapped, &swapped),
        "the two induction hypotheses of `node` must not be swapped"
    );
}

#[test]
fn test_container_map_regeneration_is_idempotent() {
    let mut env = Environment::new();
    add_mylist(&mut env);
    register_map(&mut env, "MyList");
    let outcome = env
        .synthesize_container_map(&Name::from_string("MyList"))
        .expect("regeneration succeeds");
    let ContainerMapOutcome::Decls { definitions } = outcome else {
        panic!("regeneration must still be in the v1 class");
    };
    assert!(
        definitions.is_empty(),
        "a byte-identical MyList.map must be reused, not re-emitted"
    );
}

#[test]
fn test_container_map_declines_indexed_container() {
    let mut env = Environment::new();
    // The ctor's CONSTANT result index keeps registration from promoting
    // the index to a parameter (same fixture shape as tests_all_family).
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("IdxP"),
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("IdxP.mk"),
                type_: Expr::app(
                    Expr::const_(Name::from_string("IdxP"), vec![]),
                    Expr::from_kind(ExprKind::Sort(Level::zero())),
                ),
            }],
        }],
    })
    .expect("IdxP registers");
    let outcome = env
        .synthesize_container_map(&Name::from_string("IdxP"))
        .expect("declining is not an error");
    let ContainerMapOutcome::OutOfScope { reason } = outcome else {
        panic!("an indexed container must decline");
    };
    assert!(
        reason.contains("indexed"),
        "reason names the gate: {reason}"
    );
}

#[test]
fn test_container_map_declines_field_outside_the_element_position_class() {
    // `Boxed A | mk : MyList A → Boxed A` — the field is neither exactly a
    // parameter nor exactly `Boxed A`, so there is no honest elementwise
    // transport for it. Fail closed rather than emit something ill-typed.
    let mut env = Environment::new();
    add_mylist(&mut env);
    let boxed_at = |a: Expr| Expr::app(Expr::const_(Name::from_string("Boxed"), vec![]), a);
    let type0 = Expr::type_();
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Boxed"),
            type_: Expr::pi(BinderInfo::Default, type0.clone(), type0.clone()),
            constructors: vec![Constructor {
                name: Name::from_string("Boxed.mk"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    type0,
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(
                            Expr::const_(Name::from_string("MyList"), vec![Level::zero()]),
                            Expr::bvar(0),
                        ),
                        boxed_at(Expr::bvar(1)),
                    ),
                ),
            }],
        }],
    })
    .expect("Boxed registers");
    let outcome = env
        .synthesize_container_map(&Name::from_string("Boxed"))
        .expect("declining is not an error");
    let ContainerMapOutcome::OutOfScope { reason } = outcome else {
        panic!("an out-of-class field must decline");
    };
    assert!(
        reason.contains("element position"),
        "reason names the field gate: {reason}"
    );
    assert!(
        env.get_const(&Name::from_string("Boxed.map")).is_none(),
        "a declined container must register nothing"
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

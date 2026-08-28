// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the rung-P4 generic per-container families: deep-induction
//! synthesis (`inductive_deep_induction.rs`), the functorial container map
//! (`inductive_container_map.rs`) and the relational lifting
//! (`inductive_rel_family.rs`). Acceptance = the generated All and rel
//! families pass checked `add_inductive`, the generated theorem and `C.map`
//! definition pass checked `add_decl` — the kernel referees every term —
//! `C.map` actually COMPUTES on constructors, and `C.rel` is inhabited for
//! related values while being REFUTABLE for unrelated ones.

use super::decl_builder::EnvDeclBuilder;
use super::inductive_container_map::ContainerMapOutcome;
use super::inductive_deep_induction::DeepIndOutcome;
use super::inductive_rel_family::ContainerRelOutcome;
use super::rec_apply::{close_lams, walk_telescope, RecApply};
use super::*;
use crate::expr::FVarId;
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

/// `IdxP : Type → Prop | mk : IdxP Prop` — an INDEXED family. The ctor's
/// CONSTANT result index keeps registration from promoting the index to a
/// parameter (same fixture shape as tests_all_family).
fn add_idxp(env: &mut Environment) {
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
}

/// `Boxed A | mk : MyList A → Boxed A` — a field that is neither exactly a
/// parameter nor exactly the uniform self-application. Requires `MyList`.
fn add_boxed(env: &mut Environment) {
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
    add_idxp(&mut env);
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
    add_boxed(&mut env);
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

// ── `C.rel` — the two-container relational lifting ────────────────────────

/// Register `C.rel` through the CHECKED `add_inductive` path.
fn register_rel(env: &mut Environment, container: &str) {
    let outcome = env
        .synthesize_container_rel(&Name::from_string(container))
        .expect("synthesis must not hit an invariant failure");
    let ContainerRelOutcome::Decls { families } = outcome else {
        panic!("{container} must be in the v1 container class");
    };
    assert_eq!(families.len(), 1, "one {container}.rel family");
    for fam in families {
        env.add_inductive(fam)
            .unwrap_or_else(|e| panic!("{container}.rel must pass the full kernel check: {e}"));
    }
}

#[test]
fn test_rel_family_list_generates_and_kernel_checks() {
    let mut env = Environment::new();
    add_mylist(&mut env);
    register_rel(&mut env, "MyList");

    let rel = env
        .get_inductive(&Name::from_string("MyList.rel"))
        .expect("MyList.rel registered");
    assert_eq!(
        rel.level_params,
        vec![Name::from_string("u")],
        "MyList.rel carries MyList's own level params"
    );
    assert_eq!(rel.num_params, 3, "params are A, B, R");
    assert_eq!(
        rel.num_indices, 2,
        "both container arguments are INDICES, not params"
    );
    assert_eq!(
        rel.constructor_names,
        vec![
            Name::from_string("MyList.rel.nil"),
            Name::from_string("MyList.rel.cons")
        ],
        "one lifted ctor per original ctor, same order"
    );
    // `nil` relates only to `nil`: 3 params + 0 fields.
    let nil = env
        .get_constructor(&Name::from_string("MyList.rel.nil"))
        .expect("MyList.rel.nil registered");
    assert_eq!(nil.num_fields, 0, "nil lifts to a field-less ctor");
    // `cons`: (a, l) at A, (b, l') at B, then q : R a b and q' : rel l l'.
    let cons = env
        .get_constructor(&Name::from_string("MyList.rel.cons"))
        .expect("MyList.rel.cons registered");
    assert_eq!(
        cons.num_fields, 6,
        "2 fields at A + 2 fields at B + 2 relatedness premises"
    );

    // Idempotence: regenerating against the registered family reuses.
    let ContainerRelOutcome::Decls { families } = env
        .synthesize_container_rel(&Name::from_string("MyList"))
        .expect("regeneration succeeds")
    else {
        panic!("regeneration must still be in the v1 class");
    };
    assert!(
        families.is_empty(),
        "a byte-identical MyList.rel must be reused, not re-emitted"
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

// ── `C.rel` anti-vacuity fixtures ─────────────────────────────────────────
//
// A relational lifting that held of everything would be worthless, so the
// tests below need a relation that genuinely FAILS on some element pairs,
// and observers to eliminate `MyList.rel` with. Everything here is built
// from the fixtures' own recursors and registered through checked
// `add_decl`, so the kernel referees each one.

/// `False : Prop` — no constructors.
fn add_false(env: &mut Environment) {
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("False"),
            type_: prop(),
            constructors: vec![],
        }],
    })
    .expect("False registers");
}

fn prop() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::zero()))
}

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("{name} must kernel-check: {e}"));
}

/// `Two.rec.{1} (λ _ : Two. Prop) m0 m1 arg` — large elimination into Prop.
fn two_rec_prop(m0: Expr, m1: Expr, arg: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Two.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::lam(BinderInfo::Default, two(), prop()), m0, m1, arg],
    )
}

/// `MyList.rec.{1,0} (A := Two) motive nil_m cons_m arg`.
fn mylist_rec_two(motive: Expr, nil_m: Expr, cons_m: Expr, arg: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("MyList.rec"),
            vec![Level::succ(Level::zero()), Level::zero()],
        ),
        [two(), motive, nil_m, cons_m, arg],
    )
}

/// `IsT`/`IsF`: the two singleton predicates on `Two`, and `Eq2 a b` which
/// reduces to `True` exactly when `a` and `b` are the same constructor.
/// This is the element relation the lifting is tested against — NOT a
/// relation that holds of every pair.
fn add_two_element_relation(env: &mut Environment) {
    let two_to_prop = Expr::arrow(two(), prop());
    define(
        env,
        "IsT",
        two_to_prop.clone(),
        Expr::lam(
            BinderInfo::Default,
            two(),
            two_rec_prop(t("True"), t("False"), Expr::bvar(0)),
        ),
    );
    define(
        env,
        "IsF",
        two_to_prop,
        Expr::lam(
            BinderInfo::Default,
            two(),
            two_rec_prop(t("False"), t("True"), Expr::bvar(0)),
        ),
    );
    define(
        env,
        "Eq2",
        Expr::arrow(two(), Expr::arrow(two(), prop())),
        Expr::lam(
            BinderInfo::Default,
            two(),
            Expr::lam(
                BinderInfo::Default,
                two(),
                // `a` is bvar 1, `b` is bvar 0.
                two_rec_prop(
                    Expr::app(t("IsT"), Expr::bvar(0)),
                    Expr::app(t("IsF"), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
}

/// `IsNil` and `Hd` — the observers the negative proofs eliminate with.
/// `Hd` sends `nil` to `t1` on purpose, so it separates `nil` from
/// `cons t0 _`.
fn add_list_observers(env: &mut Environment) {
    let list2 = Expr::app(
        Expr::const_(Name::from_string("MyList"), vec![Level::zero()]),
        two(),
    );
    define(
        env,
        "IsNil",
        Expr::arrow(list2.clone(), prop()),
        Expr::lam(
            BinderInfo::Default,
            list2.clone(),
            mylist_rec_two(
                Expr::lam(BinderInfo::Default, list2.clone(), prop()),
                t("True"),
                Expr::lam(
                    BinderInfo::Default,
                    two(),
                    Expr::lam(
                        BinderInfo::Default,
                        list2.clone(),
                        Expr::lam(BinderInfo::Default, prop(), t("False")),
                    ),
                ),
                Expr::bvar(0),
            ),
        ),
    );
    define(
        env,
        "Hd",
        Expr::arrow(list2.clone(), two()),
        Expr::lam(
            BinderInfo::Default,
            list2.clone(),
            mylist_rec_two(
                Expr::lam(BinderInfo::Default, list2.clone(), two()),
                t("Two.t1"),
                Expr::lam(
                    BinderInfo::Default,
                    two(),
                    Expr::lam(
                        BinderInfo::Default,
                        list2.clone(),
                        // binders: a (bvar 2), l (bvar 1), ih (bvar 0)
                        Expr::lam(BinderInfo::Default, two(), Expr::bvar(2)),
                    ),
                ),
                Expr::bvar(0),
            ),
        ),
    );
}

fn nil2() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("MyList.nil"), vec![Level::zero()]),
        two(),
    )
}

fn cons2(hd: Expr, tl: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyList.cons"), vec![Level::zero()]),
        [two(), hd, tl],
    )
}

/// `MyList.rel.{0} Two Two Eq2 l r`.
fn rel2(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyList.rel"), vec![Level::zero()]),
        [two(), two(), t("Eq2"), l, r],
    )
}

/// `MyList.rel.cons Two Two Eq2 a l b l' q q'`.
fn rel_cons(a: Expr, l: Expr, b: Expr, l2: Expr, q: Expr, q2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyList.rel.cons"), vec![Level::zero()]),
        [two(), two(), t("Eq2"), a, l, b, l2, q, q2],
    )
}

fn rel_nil() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyList.rel.nil"), vec![Level::zero()]),
        [two(), two(), t("Eq2")],
    )
}

/// Register the whole `MyList.rel`-over-`Two` fixture.
fn setup_rel_two(env: &mut Environment) {
    init_true(env);
    add_false(env);
    add_mylist(env);
    add_two(env);
    add_two_element_relation(env);
    add_list_observers(env);
    register_rel(env, "MyList");
}

/// Eliminate `MyList.rel Two Two Eq2 left right` with the generated
/// recursor and register `Π (h : …), False` as a CHECKED theorem.
///
/// `motive_body` receives the two container indices, `minor_body` the
/// minor's own (beta-normalized) telescope, and `extra_args` is applied to
/// the recursor result.
fn prove_not_rel(
    env: &mut Environment,
    name: &str,
    left: Expr,
    right: Expr,
    motive_body: &dyn Fn(&Expr, &Expr) -> Expr,
    minor_body: &dyn Fn(usize, &[(FVarId, Expr, Expr)]) -> Expr,
    extra_args: &[Expr],
) -> Result<(), EnvError> {
    let rec_name = Name::from_string("MyList.rel.rec");
    let rec = env.get_recursor(&rec_name).expect("MyList.rel.rec").clone();
    let rec_ty = rec
        .type_
        .instantiate_level_params_direct(&rec.level_params, &[Level::zero()]);
    let mut root = EnvDeclBuilder::new();
    let mut ra = RecApply::new(Expr::const_(rec_name, vec![Level::zero()]), rec_ty);
    for arg in [two(), two(), t("Eq2")] {
        ra.apply(arg).expect("param slot");
    }
    // Motive: λ (x y : MyList Two) (_ : rel x y). <motive_body x y>.
    {
        let dom = ra.peek_domain().expect("motive slot");
        let mut cb = EnvDeclBuilder::child_of(&root);
        let (locals, _) = walk_telescope(&mut cb, &dom);
        assert_eq!(locals.len(), 3, "motive takes two indices and the major");
        let body = motive_body(&locals[0].1, &locals[1].1);
        ra.apply(cb.finish_child(close_lams(&cb, &locals, body)))
            .expect("motive slot");
    }
    for i in 0..rec.num_minors as usize {
        let dom = ra.peek_domain().expect("minor slot").beta_normalize();
        let mut cb = EnvDeclBuilder::child_of(&root);
        let (locals, _) = walk_telescope(&mut cb, &dom);
        let body = minor_body(i, &locals);
        ra.apply(cb.finish_child(close_lams(&cb, &locals, body)))
            .expect("minor slot");
    }
    ra.apply(left.clone()).expect("left index");
    ra.apply(right.clone()).expect("right index");
    let hyp = rel2(left, right);
    let (h_id, h_fv) = root.fresh_local(hyp.clone());
    ra.apply(h_fv).expect("major");
    let mut body = ra.term;
    for a in extra_args {
        body = Expr::app(body, a.clone());
    }
    let value = root.finish(root.mk_lam(h_id, BinderInfo::Default, hyp.clone(), body));
    let type_ = root.finish(root.mk_pi(h_id, BinderInfo::Default, hyp, t("False")));
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    })
}

#[test]
fn test_rel_family_list_is_inhabited_for_related_values() {
    let mut env = Environment::new();
    setup_rel_two(&mut env);
    {
        // Premise of the whole fixture: `Eq2` is NOT the trivial relation.
        let tc = crate::tc::TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(
                &Expr::apps(t("Eq2"), [t("Two.t0"), t("Two.t0")]),
                &t("True")
            ),
            "Eq2 t0 t0 must reduce to True"
        );
        assert!(
            tc.is_def_eq(
                &Expr::apps(t("Eq2"), [t("Two.t0"), t("Two.t1")]),
                &t("False")
            ),
            "Eq2 t0 t1 must reduce to False — otherwise the relation is vacuous"
        );
    }

    // `[t0, t1]` is related to itself, elementwise, at both positions.
    let list = cons2(t("Two.t0"), cons2(t("Two.t1"), nil2()));
    let inner = rel_cons(
        t("Two.t1"),
        nil2(),
        t("Two.t1"),
        nil2(),
        t("True.intro"),
        rel_nil(),
    );
    let proof = rel_cons(
        t("Two.t0"),
        cons2(t("Two.t1"), nil2()),
        t("Two.t0"),
        cons2(t("Two.t1"), nil2()),
        t("True.intro"),
        inner,
    );
    // The witness goes through the FULLY CHECKED `add_decl` path (plain
    // `infer_type` runs Lean's infer-only mode and would not re-check the
    // argument types).
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("rel_witness"),
        level_params: vec![],
        type_: rel2(list.clone(), list),
        value: proof,
    })
    .expect("the relational-lifting witness must kernel-check");

    // Control for the rejection below: the very same one-cell shape IS
    // accepted when the element pair is related, so what the kernel rejects
    // next is the element relation and nothing else.
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("rel_control"),
        level_params: vec![],
        type_: rel2(cons2(t("Two.t0"), nil2()), cons2(t("Two.t0"), nil2())),
        value: rel_cons(
            t("Two.t0"),
            nil2(),
            t("Two.t0"),
            nil2(),
            t("True.intro"),
            rel_nil(),
        ),
    })
    .expect("the one-cell control witness must kernel-check");

    // The SAME shape with an element pair outside Eq2 is rejected: the
    // constructor demands a real proof of `Eq2 t0 t1`, which reduces to
    // `False`, so `True.intro` cannot stand in for it.
    let bogus = rel_cons(
        t("Two.t0"),
        nil2(),
        t("Two.t1"),
        nil2(),
        t("True.intro"),
        rel_nil(),
    );
    let rejected = env.add_decl(Declaration::Theorem {
        name: Name::from_string("rel_bogus"),
        level_params: vec![],
        type_: rel2(cons2(t("Two.t0"), nil2()), cons2(t("Two.t1"), nil2())),
        value: bogus,
    });
    assert!(
        rejected.is_err(),
        "relating t0 to t1 must not kernel-check — the lifting would be vacuous"
    );
    assert!(
        env.get_const(&Name::from_string("rel_bogus")).is_none(),
        "a rejected witness must register nothing"
    );
}

#[test]
fn test_rel_family_list_refutes_unrelated_elements_and_shapes() {
    let mut env = Environment::new();
    setup_rel_two(&mut env);

    // (1) NOT trivially true: `[t0]` is not related to `[t1]`, because the
    // heads are not `Eq2`-related. Eliminate with `λ x y _. Eq2 (Hd x) (Hd y)`:
    // the nil minor needs `Eq2 t1 t1 ≡ True`, and the cons minor is exactly
    // the element premise `Eq2 a b` the constructor carries.
    let head_motive = |x: &Expr, y: &Expr| {
        Expr::apps(
            t("Eq2"),
            [Expr::app(t("Hd"), x.clone()), Expr::app(t("Hd"), y.clone())],
        )
    };
    let head_minor = |i: usize, locals: &[(FVarId, Expr, Expr)]| {
        if i == 0 {
            assert!(locals.is_empty(), "the nil minor has no binders");
            t("True.intro")
        } else {
            assert_eq!(locals.len(), 7, "cons minor: 2+2 fields, 2 premises, 1 IH");
            // locals[4] is the element premise `Eq2 a b`.
            locals[4].1.clone()
        }
    };
    prove_not_rel(
        &mut env,
        "not_rel_t0_t1",
        cons2(t("Two.t0"), nil2()),
        cons2(t("Two.t1"), nil2()),
        &head_motive,
        &head_minor,
        &[],
    )
    .expect("¬ MyList.rel Eq2 [t0] [t1] must kernel-check");

    // (2) NOT an equality-free "same shape" relation either: values built
    // with DIFFERENT constructors are never related. Eliminate with
    // `λ x y _. IsNil x → IsNil y`; every minor is the identity, so at
    // `nil`/`cons t0 nil` the result is `True → False`.
    let shape_motive = |x: &Expr, y: &Expr| {
        Expr::arrow(
            Expr::app(t("IsNil"), x.clone()),
            Expr::app(t("IsNil"), y.clone()),
        )
    };
    let shape_minor = |_i: usize, locals: &[(FVarId, Expr, Expr)]| {
        locals
            .last()
            .expect("each minor ends with the IsNil hypothesis")
            .1
            .clone()
    };
    prove_not_rel(
        &mut env,
        "not_rel_nil_cons",
        nil2(),
        cons2(t("Two.t0"), nil2()),
        &shape_motive,
        &shape_minor,
        &[t("True.intro")],
    )
    .expect("¬ MyList.rel Eq2 nil (cons t0 nil) must kernel-check");

    for name in ["not_rel_t0_t1", "not_rel_nil_cons"] {
        let thm = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} registered"));
        assert!(
            crate::inductive::mentions_name(&thm.type_, &Name::from_string("MyList.rel")),
            "{name} must be a statement ABOUT the lifting"
        );
    }
}

// ── `C.rel` over a two-recursive-field container ──────────────────────────

fn tree_leaf(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyTree.leaf"), vec![Level::zero()]),
        [two(), x],
    )
}

fn tree_node(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyTree.node"), vec![Level::zero()]),
        [two(), l, r],
    )
}

fn tree_rel(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyTree.rel"), vec![Level::zero()]),
        [two(), two(), t("Eq2"), l, r],
    )
}

fn tree_rel_leaf(a: Expr, b: Expr, q: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyTree.rel.leaf"), vec![Level::zero()]),
        [two(), two(), t("Eq2"), a, b, q],
    )
}

fn tree_rel_node(l1: Expr, r1: Expr, l2: Expr, r2: Expr, q1: Expr, q2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyTree.rel.node"), vec![Level::zero()]),
        [two(), two(), t("Eq2"), l1, r1, l2, r2, q1, q2],
    )
}

#[test]
fn test_rel_family_tree_pairs_fields_positionally() {
    // `node` has TWO self-recursive fields, so the two recursive premises
    // have the same shape and can only be told apart by WHICH fields they
    // relate. An asymmetric tree pins the pairing.
    let mut env = Environment::new();
    init_true(&mut env);
    add_false(&mut env);
    add_mytree(&mut env);
    add_two(&mut env);
    add_two_element_relation(&mut env);
    register_rel(&mut env, "MyTree");

    let leaf = env
        .get_constructor(&Name::from_string("MyTree.rel.leaf"))
        .expect("MyTree.rel.leaf registered");
    assert_eq!(leaf.num_fields, 3, "leaf: one field per side + one premise");
    let node = env
        .get_constructor(&Name::from_string("MyTree.rel.node"))
        .expect("MyTree.rel.node registered");
    assert_eq!(
        node.num_fields, 6,
        "node: two fields per side + two recursive premises"
    );

    let q_left = tree_rel_leaf(t("Two.t0"), t("Two.t0"), t("True.intro"));
    let q_right = tree_rel_leaf(t("Two.t1"), t("Two.t1"), t("True.intro"));
    let tree = tree_node(tree_leaf(t("Two.t0")), tree_leaf(t("Two.t1")));

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("tree_rel_witness"),
        level_params: vec![],
        type_: tree_rel(tree.clone(), tree.clone()),
        value: tree_rel_node(
            tree_leaf(t("Two.t0")),
            tree_leaf(t("Two.t1")),
            tree_leaf(t("Two.t0")),
            tree_leaf(t("Two.t1")),
            q_left.clone(),
            q_right.clone(),
        ),
    })
    .expect("the node witness must kernel-check");

    // The same premises in the other order relate the WRONG subtrees.
    let crossed = env.add_decl(Declaration::Theorem {
        name: Name::from_string("tree_rel_crossed"),
        level_params: vec![],
        type_: tree_rel(tree.clone(), tree),
        value: tree_rel_node(
            tree_leaf(t("Two.t0")),
            tree_leaf(t("Two.t1")),
            tree_leaf(t("Two.t0")),
            tree_leaf(t("Two.t1")),
            q_right,
            q_left,
        ),
    });
    assert!(
        crossed.is_err(),
        "the two recursive premises must be pinned to their own field pairs"
    );
}

// ── `C.rel` declines — fail closed, register nothing ──────────────────────

#[test]
fn test_rel_family_declines_indexed_container() {
    let mut env = Environment::new();
    add_idxp(&mut env);
    let outcome = env
        .synthesize_container_rel(&Name::from_string("IdxP"))
        .expect("declining is not an error");
    let ContainerRelOutcome::OutOfScope { reason } = outcome else {
        panic!("an indexed container must decline");
    };
    assert!(
        reason.contains("indexed"),
        "reason names the gate: {reason}"
    );
    assert!(
        env.get_inductive(&Name::from_string("IdxP.rel")).is_none(),
        "a declined container must register nothing"
    );
}

#[test]
fn test_rel_family_declines_field_outside_the_element_position_class() {
    // `Boxed A | mk : MyList A → Boxed A` — the field is neither exactly a
    // parameter nor exactly `Boxed A`, so there is no honest elementwise
    // relatedness premise for it.
    let mut env = Environment::new();
    add_mylist(&mut env);
    add_boxed(&mut env);
    let outcome = env
        .synthesize_container_rel(&Name::from_string("Boxed"))
        .expect("declining is not an error");
    let ContainerRelOutcome::OutOfScope { reason } = outcome else {
        panic!("an out-of-class field must decline");
    };
    assert!(
        reason.contains("element position"),
        "reason names the field gate: {reason}"
    );
    assert!(
        env.get_inductive(&Name::from_string("Boxed.rel")).is_none(),
        "a declined container must register nothing"
    );
}

#[test]
fn test_rel_family_declines_nested_container() {
    let mut env = Environment::new();
    add_mylist(&mut env);
    add_term(&mut env);
    let outcome = env
        .synthesize_container_rel(&Name::from_string("Term"))
        .expect("declining is not an error");
    let ContainerRelOutcome::OutOfScope { reason } = outcome else {
        panic!("a nested container must decline");
    };
    assert!(reason.contains("nested"), "reason names the gate: {reason}");
}

// ── `C.rel` over a TWO-parameter container ────────────────────────────────

/// `MyPair.{u} : Type u → Type u → Type u | mk : A → B → MyPair A B`.
fn add_mypair(env: &mut Environment) {
    let u = Name::from_string("u");
    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("MyPair"),
            type_: Expr::pi(
                BinderInfo::Default,
                sort_u(&u),
                Expr::pi(BinderInfo::Default, sort_u(&u), sort_u(&u)),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("MyPair.mk"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    sort_u(&u),
                    Expr::pi(
                        BinderInfo::Implicit,
                        sort_u(&u),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(1),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::bvar(1),
                                Expr::apps(
                                    Expr::const_(
                                        Name::from_string("MyPair"),
                                        vec![Level::param(u.clone())],
                                    ),
                                    [Expr::bvar(3), Expr::bvar(2)],
                                ),
                            ),
                        ),
                    ),
                ),
            }],
        }],
    })
    .expect("MyPair registers");
}

/// `Ne2 a b` reduces to `True` exactly when `a` and `b` DIFFER — the second
/// element relation, deliberately different from `Eq2`.
fn add_ne2(env: &mut Environment) {
    define(
        env,
        "Ne2",
        Expr::arrow(two(), Expr::arrow(two(), prop())),
        Expr::lam(
            BinderInfo::Default,
            two(),
            Expr::lam(
                BinderInfo::Default,
                two(),
                two_rec_prop(
                    Expr::app(t("IsF"), Expr::bvar(0)),
                    Expr::app(t("IsT"), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
}

fn pair_mk(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyPair.mk"), vec![Level::zero()]),
        [two(), two(), x, y],
    )
}

fn pair_rel(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyPair.rel"), vec![Level::zero()]),
        [two(), two(), two(), two(), t("Eq2"), t("Ne2"), l, r],
    )
}

fn pair_rel_mk(x: Expr, y: Expr, u: Expr, v: Expr, q1: Expr, q2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MyPair.rel.mk"), vec![Level::zero()]),
        [
            two(),
            two(),
            two(),
            two(),
            t("Eq2"),
            t("Ne2"),
            x,
            y,
            u,
            v,
            q1,
            q2,
        ],
    )
}

#[test]
fn test_rel_family_two_params_keeps_each_relation_at_its_own_position() {
    // With m = 2 the two element relations are DIFFERENT (`Eq2` vs `Ne2`),
    // so a lifting that mixed up which relation guards which component —
    // or which component of the right-hand value it relates to — cannot
    // typecheck the witness below.
    let mut env = Environment::new();
    init_true(&mut env);
    add_false(&mut env);
    add_two(&mut env);
    add_two_element_relation(&mut env);
    add_ne2(&mut env);
    add_mypair(&mut env);
    register_rel(&mut env, "MyPair");

    let rel = env
        .get_inductive(&Name::from_string("MyPair.rel"))
        .expect("MyPair.rel registered");
    assert_eq!(rel.num_params, 6, "params are A₁ A₂ B₁ B₂ R₁ R₂");
    assert_eq!(rel.num_indices, 2, "both containers are indices");
    let mk = env
        .get_constructor(&Name::from_string("MyPair.rel.mk"))
        .expect("MyPair.rel.mk registered");
    assert_eq!(
        mk.num_fields, 6,
        "two fields per side plus one premise per field"
    );

    // `(t0, t0)` relates to `(t0, t1)`: equal firsts, different seconds.
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("pair_rel_witness"),
        level_params: vec![],
        type_: pair_rel(
            pair_mk(t("Two.t0"), t("Two.t0")),
            pair_mk(t("Two.t0"), t("Two.t1")),
        ),
        value: pair_rel_mk(
            t("Two.t0"),
            t("Two.t0"),
            t("Two.t0"),
            t("Two.t1"),
            t("True.intro"),
            t("True.intro"),
        ),
    })
    .expect("the two-parameter witness must kernel-check");

    // Relating `(t0, t0)` to itself fails: `Ne2 t0 t0` reduces to `False`,
    // so the SECOND relation is genuinely demanded at the second component.
    let rejected = env.add_decl(Declaration::Theorem {
        name: Name::from_string("pair_rel_bogus"),
        level_params: vec![],
        type_: pair_rel(
            pair_mk(t("Two.t0"), t("Two.t0")),
            pair_mk(t("Two.t0"), t("Two.t0")),
        ),
        value: pair_rel_mk(
            t("Two.t0"),
            t("Two.t0"),
            t("Two.t0"),
            t("Two.t0"),
            t("True.intro"),
            t("True.intro"),
        ),
    });
    assert!(
        rejected.is_err(),
        "R₂ must really guard the second component"
    );
}

/// A container with TWO fields of the SAME element param.
///
/// `MyPair2 A | mk : A → A → MyPair2 A`. This is the class where crossing the
/// two relatedness premises stays WELL-TYPED — both are `R _ _` at the same
/// pair of types — so neither the kernel nor any differently-typed fixture
/// notices a swap. The `m = 2` test above cannot catch it (its two relations
/// have different types); `MyList`/`MyTree` cannot (one element field each).
fn add_mypair2(env: &mut Environment) {
    let u = Name::from_string("u");
    let mypair2 = Name::from_string("MyPair2");
    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: mypair2.clone(),
            type_: Expr::pi(BinderInfo::Default, sort_u(&u), sort_u(&u)),
            constructors: vec![Constructor {
                name: Name::from_string("MyPair2.mk"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    sort_u(&u),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(0),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(1),
                            Expr::app(
                                Expr::const_(mypair2.clone(), vec![Level::param(u.clone())]),
                                Expr::bvar(2),
                            ),
                        ),
                    ),
                ),
            }],
        }],
    })
    .expect("MyPair2 fixture must register");
}

/// The two premises must stay at their OWN field positions.
///
/// Found by the reviewer of this rung, not by its author: the implementation is
/// correct here, but nothing exercised the one shape where a cross survives
/// typechecking. `Eq2` is asymmetric enough to discriminate — relating
/// `mk t0 t1` to `mk t1 t0` requires `Eq2 t0 t1`, which reduces to `False`, so
/// only a CROSSED lifting would accept it.
#[test]
fn test_rel_family_same_param_twice_keeps_premises_at_their_own_positions() {
    let mut env = Environment::new();
    init_true(&mut env);
    add_false(&mut env);
    add_two(&mut env);
    add_two_element_relation(&mut env);
    add_mypair2(&mut env);
    register_rel(&mut env, "MyPair2");

    let rel = env
        .get_inductive(&Name::from_string("MyPair2.rel"))
        .expect("MyPair2.rel registered");
    assert_eq!(rel.num_params, 3, "params are A, B, R");
    assert_eq!(rel.num_indices, 2, "both containers are indices");

    let p2 = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("MyPair2.mk"), vec![Level::zero()]),
            [two(), x, y],
        )
    };
    let p2_rel = |l: Expr, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("MyPair2.rel"), vec![Level::zero()]),
            [two(), two(), t("Eq2"), l, r],
        )
    };
    let p2_rel_mk = |x: Expr, y: Expr, u: Expr, v: Expr, q1: Expr, q2: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("MyPair2.rel.mk"), vec![Level::zero()]),
            [two(), two(), t("Eq2"), x, y, u, v, q1, q2],
        )
    };

    // CONTROL: `mk t0 t1` relates to itself — both premises hold pointwise.
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("pair2_rel_witness"),
        level_params: vec![],
        type_: p2_rel(p2(t("Two.t0"), t("Two.t1")), p2(t("Two.t0"), t("Two.t1"))),
        value: p2_rel_mk(
            t("Two.t0"),
            t("Two.t1"),
            t("Two.t0"),
            t("Two.t1"),
            t("True.intro"),
            t("True.intro"),
        ),
    })
    .expect("the pointwise-related witness must kernel-check");

    // THE DISCRIMINATOR: `mk t0 t1` must NOT relate to `mk t1 t0`. That needs
    // `Eq2 t0 t1`, which reduces to `False`. A lifting whose premises were
    // crossed would accept this, and would still typecheck everywhere else.
    let crossed = env.add_decl(Declaration::Theorem {
        name: Name::from_string("pair2_rel_crossed"),
        level_params: vec![],
        type_: p2_rel(p2(t("Two.t0"), t("Two.t1")), p2(t("Two.t1"), t("Two.t0"))),
        value: p2_rel_mk(
            t("Two.t0"),
            t("Two.t1"),
            t("Two.t1"),
            t("Two.t0"),
            t("True.intro"),
            t("True.intro"),
        ),
    });
    assert!(
        crossed.is_err(),
        "each premise must guard its OWN field position — a crossed lifting \
         would relate `mk t0 t1` to `mk t1 t0`"
    );
}

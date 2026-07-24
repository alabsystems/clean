// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for noConfusion per-field sort level correctness (#2044).
//!
//! Verifies that `compute_ctor_field_sort_levels` propagates errors instead of
//! silently mapping `infer_sort` failures to `Level::zero()`, and that
//! noConfusionType correctly handles multi-constructor and multi-field inductives.

use super::*;
use crate::env::Environment;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::tc::TypeChecker;

/// Helper: create a 3-constructor enum (no fields per constructor).
fn make_colour_env() -> Environment {
    let mut env = Environment::new();
    let colour = Name::from_string("Colour");
    let colour_ref = Expr::const_(colour.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: colour.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Colour.red"),
                    type_: colour_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Colour.green"),
                    type_: colour_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Colour.blue"),
                    type_: colour_ref,
                },
            ],
        }],
    };
    env.add_inductive(decl)
        .expect("invariant: Colour inductive is well-formed");
    env.init_eq()
        .expect("invariant: Eq init succeeds after inductive registration");
    env
}

/// Helper: create env with Nat + Wrap (2 Nat fields).
fn make_wrap_env() -> Environment {
    let mut env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    })
    .expect("invariant: Nat inductive is well-formed");
    env.init_eq()
        .expect("invariant: Eq init succeeds after Nat registration");

    let wrap = Name::from_string("Wrap");
    let wrap_ref = Expr::const_(wrap.clone(), vec![]);
    let mk_type = Expr::arrow(nat_ref.clone(), Expr::arrow(nat_ref, wrap_ref));
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: wrap,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("invariant: Wrap inductive is well-formed");
    env
}

/// Helper: check if an expression is an Eq application (Eq _ _ _).
fn is_eq_app(e: &Expr) -> bool {
    if let ExprKind::App(f, _) = &e.kind {
        if let ExprKind::App(f2, _) = &f.as_ref().kind {
            if let ExprKind::App(f3, _) = &f2.as_ref().kind {
                if let ExprKind::Const(name, _) = &f3.as_ref().kind {
                    return name.to_string() == "Eq";
                }
            }
        }
    }
    false
}

/// Helper: count the number of Eq arrows in a Pi chain before the final Sort.
fn count_eq_arrows(e: &Expr) -> usize {
    let mut count = 0;
    let mut cur = e;
    while let ExprKind::Pi(_, domain, body) = &cur.kind {
        if is_eq_app(domain) {
            count += 1;
        }
        cur = body.as_ref();
    }
    count
}

/// 3-constructor enum: all 9 pairs produce correct noConfusionType.
/// Same ctor → (P → P), different ctor → P.
#[test]
fn test_3_ctor_all_pairs() {
    let env = make_colour_env();
    let tc = TypeChecker::new(&env);
    let ctors: Vec<(&str, Expr)> = ["red", "green", "blue"]
        .iter()
        .map(|c| {
            (
                *c,
                Expr::const_(Name::from_string(&format!("Colour.{c}")), vec![]),
            )
        })
        .collect();
    let nct = Expr::const_(
        Name::from_string("Colour.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );
    for (na, ca) in &ctors {
        for (nb, cb) in &ctors {
            let app = Expr::app(
                Expr::app(Expr::app(nct.clone(), Expr::type_()), ca.clone()),
                cb.clone(),
            );
            let result = tc.whnf(&app);
            if na == nb {
                assert!(
                    matches!(&result.kind, ExprKind::Pi(_, _, _)),
                    "{na}/{nb}: Expected Pi (P → P), got: {result:?}"
                );
            } else {
                assert!(
                    matches!(&result.kind, ExprKind::Sort(_)),
                    "{na}/{nb}: Expected Sort (P), got: {result:?}"
                );
            }
        }
    }
}

/// 2-field inductive: noConfusionType includes 2 Eq arrows for Type-valued fields.
#[test]
fn test_multi_field_eq_arrows() {
    let env = make_wrap_env();
    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nct = Expr::const_(
        Name::from_string("Wrap.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );
    let mk = Expr::const_(Name::from_string("Wrap.mk"), vec![]);
    let mk00 = Expr::app(Expr::app(mk, zero.clone()), zero);

    let app = Expr::app(Expr::app(Expr::app(nct, Expr::type_()), mk00.clone()), mk00);
    let result = tc.whnf(&app);

    // Result: ((Eq Nat 0 0 → Eq Nat 0 0 → Type) → Type)
    // Outer Pi must be a Pi with 2 Eq arrows in its domain.
    assert!(
        matches!(&result.kind, ExprKind::Pi(_, _, _)),
        "Expected Pi for Wrap.mk/Wrap.mk same-ctor case, got: {result:?}"
    );
    if let ExprKind::Pi(_, domain, _) = &result.kind {
        let eq_count = count_eq_arrows(domain);
        assert_eq!(eq_count, 2, "Expected 2 Eq arrows for 2 Type fields");
    }

    let result_ty = tc.infer_type(&result).expect("should be well-typed");
    assert!(matches!(&result_ty.kind, ExprKind::Sort(_)));
}

/// Helper: check if an expression is an HEq application (`@HEq.{l} A a B b`).
///
/// Under the v4.30 heterogeneous convention
/// (designs/2026-07-03-noconfusion-ctoridx-convention.md §3) a field whose
/// type mentions a PARAM gets an `HEq` diagonal hypothesis, not `Eq`.
fn is_heq_app(e: &Expr) -> bool {
    if let ExprKind::Const(name, _) = &e.get_app_fn().kind {
        return name.to_string() == "HEq";
    }
    false
}

/// Helper: count HEq arrows in a Pi chain before the final Sort.
fn count_heq_arrows(e: &Expr) -> usize {
    let mut count = 0;
    let mut cur = e;
    while let ExprKind::Pi(_, domain, body) = &cur.kind {
        if is_heq_app(domain) {
            count += 1;
        }
        cur = body.as_ref();
    }
    count
}

/// Helper: extract the universe level from the first HEq application in a Pi
/// domain. Returns the level from `@HEq.{l} ...` or None if no HEq found.
fn extract_heq_level(e: &Expr) -> Option<Level> {
    let mut cur = e;
    while let ExprKind::Pi(_, domain, body) = &cur.kind {
        let head = domain.get_app_fn();
        if let ExprKind::Const(name, levels) = &head.kind {
            if name.to_string() == "HEq" && !levels.is_empty() {
                return Some(levels[0].clone());
            }
        }
        cur = body.as_ref();
    }
    None
}

/// Helper: create env with Nat + universe-polymorphic MyBox.{u}.
///
/// ```text
/// MyBox.{u} : Type u → Type u
/// MyBox.mk  : {α : Type u} → α → MyBox.{u} α
/// ```
///
/// The field `val : α` has sort level `succ u` (since `α : Type u = Sort (succ u)`).
/// With the bug (#1800), `build_no_confusion` would silently use `Level::zero()`
/// for the field sort, producing `Eq.{0}` instead of `Eq.{succ u}`.
fn make_mybox_env() -> Environment {
    let mut env = Environment::new();

    // Register Nat first (needed as a concrete type to instantiate MyBox)
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    })
    .expect("invariant: Nat inductive is well-formed");

    env.init_eq()
        .expect("invariant: Eq init succeeds after Nat registration");
    // HEq before the parameterized MyBox: the v4.30 heterogeneous noConfusion
    // convention (designs/2026-07-03-noconfusion-ctoridx-convention.md) uses
    // HEq for param-mentioning fields.
    env.init_heq()
        .expect("invariant: HEq init succeeds after Eq registration");

    // Register MyBox.{u} : Type u → Type u
    let u = Name::from_string("u");
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
    let mybox = Name::from_string("MyBox");

    // MyBox.{u} : Type u → Type u
    // Pi (α : Type u). Type u
    let mybox_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

    // MyBox.mk : (α : Type u) → α → MyBox.{u} α
    // Pi (α : Type u). Pi (val : BVar(0)). App(MyBox.{u}, BVar(1))
    //   Under 2 binders: BVar(0) = val, BVar(1) = α
    let mk_type = Expr::pi(
        BinderInfo::Default,
        type_u,
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // val : α
            Expr::app(
                Expr::const_(mybox.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1), // MyBox α
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: mybox,
            type_: mybox_type,
            constructors: vec![Constructor {
                name: Name::from_string("MyBox.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("invariant: MyBox inductive is well-formed");
    env
}

#[test]
fn test_parameterized_no_confusion_waits_for_late_heq_then_heals() {
    let mut env = Environment::new();
    env.init_punit()
        .expect("PUnit is required by noConfusionType");
    let u = Name::from_string("u");
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
    let late_box = Name::from_string("LateBox");
    let late_box_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
    let late_box_mk_type = Expr::pi(
        BinderInfo::Default,
        type_u,
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(
                Expr::const_(late_box.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: late_box.clone(),
            type_: late_box_type,
            constructors: vec![Constructor {
                name: Name::from_string("LateBox.mk"),
                type_: late_box_mk_type,
            }],
        }],
    })
    .expect("declare parameterized LateBox before equality");

    env.init_eq().expect("initialize Eq without HEq");
    let generation_before_pending_retry = env.generation();
    let pending = env.regenerate_missing_no_confusion_with_report();
    assert!(pending.diagnostics.iter().any(|diagnostic| {
        diagnostic.block == vec![late_box.clone()]
            && matches!(
                diagnostic.issue,
                crate::env::NoConfusionRegenerationIssue::PendingHeterogeneousEquality
            )
    }));
    assert_eq!(
        env.generation(),
        generation_before_pending_retry,
        "a prerequisite-only retry must not mutate the environment"
    );
    for suffix in ["noConfusionType", "noConfusion"] {
        let name = Name::from_string(&format!("LateBox.{suffix}"));
        assert_ne!(
            env.declaration_verification(&name),
            Some(crate::env::DeclarationVerification::FullKernelCheck),
            "{name} cannot be authoritative before HEq"
        );
    }

    env.init_heq()
        .expect("late HEq should repair the canonical heterogeneous pair");
    for suffix in ["noConfusionType", "noConfusion"] {
        let name = Name::from_string(&format!("LateBox.{suffix}"));
        assert_eq!(
            env.declaration_verification(&name),
            Some(crate::env::DeclarationVerification::FullKernelCheck),
            "{name} must be rooted after the complete HEq surface exists"
        );
    }
}

/// Universe-polymorphic inductive: field sort level must track the universe param,
/// not silently fall back to Level::zero (#1800).
///
/// MyBox.{u} has one field of type `α : Type u`. The field sort is `succ u`.
/// When instantiated at u=0, the Eq in noConfusionType must use `Eq.{1}`, not `Eq.{0}`.
/// The old code (`.unwrap_or_default()` + `.unwrap_or(Level::zero())`) would produce
/// `Eq.{0}` for all fields, making the noConfusion value ill-typed at higher universes.
#[test]
fn test_parametric_field_sort_level_not_zero() {
    let env = make_mybox_env();
    let tc = TypeChecker::new(&env);

    // Instantiate at u=0: MyBox.{0} works on Type 0 values.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero_val = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let mk = Expr::const_(Name::from_string("MyBox.mk"), vec![Level::zero()]);
    let mk_nat_zero = Expr::app(Expr::app(mk, nat.clone()), zero_val);

    // v4.30 heterogeneous convention
    // (designs/2026-07-03-noconfusion-ctoridx-convention.md §3):
    // noConfusionType.{v, u} :
    //   Sort v → {α : Type u} → MyBox α → {α' : Type u} → MyBox α' → Sort v
    // Apply: nct P α a α' b (P FIRST; the second major has its own params).
    let nct = Expr::const_(
        Name::from_string("MyBox.noConfusionType"),
        vec![Level::succ(Level::zero()), Level::zero()], // v=succ(0), u=0
    );
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(nct, Expr::type_()), // P = Type
                    nat.clone(),                   // α = Nat
                ),
                mk_nat_zero.clone(), // a = MyBox.mk Nat 0
            ),
            nat.clone(), // α' = Nat
        ),
        mk_nat_zero, // b = MyBox.mk Nat 0
    );
    let result = tc.whnf(&app);

    // Same-constructor case: reduces to (HEq.{1} Nat 0 Nat 0 → Type) → Type.
    // The field `val : α` MENTIONS the param α, so under the v4.30 mkEqHEq
    // rule its diagonal hypothesis is HEq (a-side at α, b-side at α'), not Eq.
    assert!(
        matches!(&result.kind, ExprKind::Pi(_, _, _)),
        "Expected Pi for MyBox.mk/MyBox.mk diagonal, got: {result:?}"
    );

    if let ExprKind::Pi(_, domain, _) = &result.kind {
        let heq_count = count_heq_arrows(domain);
        assert_eq!(
            heq_count, 1,
            "Expected 1 HEq arrow for 1 param-mentioning field"
        );
        assert_eq!(
            count_eq_arrows(domain),
            0,
            "param-mentioning field must use HEq, not Eq, under the v4.30 rule"
        );

        // The HEq universe level must be succ(0) = 1, NOT 0.
        // Level::zero would mean Prop-level equality, which is wrong for a Type field.
        let heq_level =
            extract_heq_level(domain).expect("should find HEq in noConfusionType diagonal domain");
        assert!(
            !heq_level.is_zero(),
            "Bug #1800: HEq level should be succ(0), not zero for Type-valued field"
        );
    }
}

/// The noConfusion value body must type-check with correct field sort levels.
///
/// When `build_no_confusion` used `.unwrap_or_default()`, the Eq.refl/HEq.refl
/// universe levels in the value body would be Level::zero, causing a type mismatch
/// between the noConfusionType (which has correct levels via `build_no_confusion_type`)
/// and the noConfusion value body.
#[test]
fn test_parametric_no_confusion_value_typechecks() {
    let env = make_mybox_env();
    let tc = TypeChecker::new(&env);

    // The noConfusion constant should have an inferrable type.
    let nc = Expr::const_(
        Name::from_string("MyBox.noConfusion"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let nc_type = tc
        .infer_type(&nc)
        .expect("noConfusion should be well-typed — #1800 fix ensures correct sort levels");
    assert!(
        matches!(&nc_type.kind, ExprKind::Pi(_, _, _)),
        "noConfusion type should be a Pi chain"
    );
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Regression (Trust verified lane, 2026-10-07): the counts that size a vector
//! up front during recursor derivation are bounded where the vector is built.
//!
//! - Nested admission: `InductiveDecl::num_level_params` (a `u32` header field)
//!   sized a fresh level vector at EVERY rewritten occurrence site, before the
//!   mutual admission refused the count. A forged `u32::MAX` asked for tens of
//!   GB there; it is now refused at entry with the
//!   `Derivation` reject recursor derivation gives the same count (wrapped in
//!   `NestedError::Aux`, as every mutual-admission reject is), and the vector
//!   is built once and shared. Measured on the base (01ffe3108) at
//!   `MAX_DERIVED_ARITY + 1`: still a reject, `Aux { UniverseTooLarge }`.
//! - Width: a recursor is derived for at most `recursor::MAX_INDUCTIVE_WIDTH`
//!   constructors (single) or types (mutual). Each derived element is wider than
//!   its source, so the up-front allocation outgrew the input; above the bound
//!   admission is a typed `AdmitError::Derivation`. Measured on the base: a
//!   2^20 + 1 constructor declaration overflowed the stack and aborted.
//!
//! Every new outcome is a reject of an input that was never admissible in
//! practice; real declarations (the controls below) are unaffected.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::recursor::{MAX_DERIVED_ARITY, MAX_INDUCTIVE_WIDTH};
use clean_ck0::{
    add_inductive, add_inductive_nested, AdmitError, Constructor, Env, InductiveDecl, MinimalEnv,
    Name, NestedError, RawExpr, RawLevel, Term,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}
fn r_sort1() -> RawExpr {
    RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)))
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_const_p(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

/// An env with `List.{u} (A : Sort u)` admitted, to nest in.
fn env_with_list() -> MinimalEnv {
    let b = MinimalEnv::new()
        .with_const(n("List"), 1)
        .with_const(n("List.nil"), 1)
        .with_const(n("List.cons"), 1);
    let sort_u = RawExpr::Sort(RawLevel::Param(0));
    let list_a = |db: u32| {
        r_app(
            r_const_p("List", vec![RawLevel::Param(0)]),
            RawExpr::BVar(db),
        )
    };
    let decl = InductiveDecl {
        name: n("List"),
        num_level_params: 1,
        num_params: 1,
        type_: vlvl(&b, &r_pi(sort_u.clone(), sort_u.clone()), 1),
        constructors: vec![
            Constructor {
                name: n("List.nil"),
                type_: vlvl(&b, &r_pi(sort_u.clone(), list_a(0)), 1),
            },
            Constructor {
                name: n("List.cons"),
                type_: vlvl(
                    &b,
                    &r_pi(sort_u, r_pi(RawExpr::BVar(0), r_pi(list_a(1), list_a(2)))),
                    1,
                ),
            },
        ],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, decl).expect("List admits");
    env
}

/// `RoseTree : Type` with `RoseTree.mk : List.{1} RoseTree -> RoseTree`, at a
/// chosen level-param count (its terms use none).
fn rosetree_decl(num_level_params: u32) -> InductiveDecl {
    let b = MinimalEnv::new()
        .with_const(n("RoseTree"), 0)
        .with_const(n("RoseTree.mk"), 0)
        .with_const(n("List"), 1);
    let lvl1 = RawLevel::Succ(Box::new(RawLevel::Zero));
    let field = r_app(r_const_p("List", vec![lvl1]), r_const("RoseTree"));
    InductiveDecl {
        name: n("RoseTree"),
        num_level_params,
        num_params: 0,
        type_: vlvl(&b, &r_sort1(), 0),
        constructors: vec![Constructor {
            name: n("RoseTree.mk"),
            type_: vlvl(&b, &r_pi(field, r_const("RoseTree")), 0),
        }],
    }
}

#[test]
fn nested_inductive_with_forged_level_param_count_is_rejected_not_allocated() {
    for count in [MAX_DERIVED_ARITY.saturating_add(1), u32::MAX] {
        let mut env = env_with_list();
        match add_inductive_nested(&mut env, rosetree_decl(count)) {
            Err(NestedError::Aux {
                ind,
                source: AdmitError::Derivation { detail, .. },
            }) => {
                assert_eq!(ind, n("RoseTree"));
                assert!(
                    detail.contains("too many universe level params"),
                    "unexpected detail: {detail}"
                );
            }
            other => panic!("expected a too-many-level-params reject, got {other:?}"),
        }
        assert!(
            env.recursor_type(&n("RoseTree")).is_none(),
            "nothing admitted"
        );
    }
}

#[test]
fn nested_inductive_control_is_admitted() {
    let mut env = env_with_list();
    add_inductive_nested(&mut env, rosetree_decl(0)).expect("RoseTree admits");
    assert!(env.recursor_type(&n("RoseTree._List")).is_some());
}

/// `Wide : Type` with `count` field-less constructors `Wide.c<i> : Wide`.
fn wide_decl(count: usize) -> InductiveDecl {
    let b = MinimalEnv::new().with_const(n("Wide"), 0);
    let ty = vlvl(&b, &r_sort1(), 0);
    let ctor_ty = vlvl(&b, &r_const("Wide"), 0);
    InductiveDecl {
        name: n("Wide"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: (0..count)
            .map(|i| Constructor {
                name: n(&format!("Wide.c{i}")),
                type_: ctor_ty.clone(),
            })
            .collect(),
    }
}

#[test]
fn single_inductive_wider_than_the_limit_is_rejected() {
    let mut env = MinimalEnv::new();
    match add_inductive(&mut env, wide_decl(MAX_INDUCTIVE_WIDTH + 1)) {
        Err(AdmitError::Derivation { detail, .. }) => assert!(
            detail.contains("too many constructors"),
            "unexpected detail: {detail}"
        ),
        other => panic!("expected a too-many-constructors reject, got {other:?}"),
    }
    assert!(env.recursor_type(&n("Wide")).is_none(), "nothing admitted");
}

#[test]
fn wide_inductive_control_is_admitted() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, wide_decl(64)).expect("64 constructors admit");
    assert!(env.recursor_type(&n("Wide")).is_some());
}

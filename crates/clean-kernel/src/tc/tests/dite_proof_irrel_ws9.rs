// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS9 proof-irrelevance regressions surfaced by the `dif_pos` / `dif_neg` /
//! `instDecidableDite` family.
//!
//! After `dite c (Decidable.isTrue c h) t e` reduces to `t h` (fixed in the
//! native `dite` reducer — see `tests_native_reducers_init.rs`), the kernel must
//! still see `t h =?= t hc` for two distinct proofs `h`, `hc` of the same Prop
//! by proof irrelevance. These tests pin the proof-irrelevance baseline for the
//! distinct-fvar / local-Prop shapes that occur inside the reduced match.

use super::*;
use crate::env::Declaration;

#[test]
fn repro_b_direct_distinct_fvars_same_prop() {
    let mut env = Environment::new();
    // p : Prop  (a Prop-valued axiom)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let mut tc = TypeChecker::new(&env);
    let p_const = Expr::const_(Name::from_string("p"), vec![]);
    // x : p, x1 : p — two distinct fvars of the same Prop
    let x =
        tc.local_context_mut()
            .push(Name::from_string("x"), p_const.clone(), BinderInfo::Default);
    let x1 = tc.local_context_mut().push(
        Name::from_string("x1"),
        p_const.clone(),
        BinderInfo::Default,
    );
    let xe = Expr::from_kind(ExprKind::FVar(x));
    let x1e = Expr::from_kind(ExprKind::FVar(x1));
    // Direct: x =?= x1 should be true by proof irrel
    assert!(
        tc.is_def_eq(&xe, &x1e),
        "distinct fvars of same Prop must be def_eq by proof irrel"
    );
}

#[test]
fn repro_b_app_distinct_fvars_same_prop() {
    let mut env = Environment::new();
    // p : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    // A : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    // f : p -> A  (consumes a proof, yields a value of A, NOT a Prop result)
    let p_const = Expr::const_(Name::from_string("p"), vec![]);
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, p_const.clone(), a_const.clone()),
    })
    .unwrap();

    let mut tc = TypeChecker::new(&env);
    let f_const = Expr::const_(Name::from_string("f"), vec![]);
    let x =
        tc.local_context_mut()
            .push(Name::from_string("x"), p_const.clone(), BinderInfo::Default);
    let x1 = tc.local_context_mut().push(
        Name::from_string("x1"),
        p_const.clone(),
        BinderInfo::Default,
    );
    let fx = Expr::app(f_const.clone(), Expr::from_kind(ExprKind::FVar(x)));
    let fx1 = Expr::app(f_const.clone(), Expr::from_kind(ExprKind::FVar(x1)));
    // f x =?= f x1 : both yield A. The args x, x1 are proofs of p, def_eq by proof irrel.
    assert!(
        tc.is_def_eq(&fx, &fx1),
        "f x =?= f x1 must hold: args are proof-irrelevant"
    );
}

#[test]
fn repro_b_app_distinct_fvars_local_prop() {
    // Mirrors the dif_pos failure: the Prop is a LOCAL fvar `c : Prop`, not a
    // global Const. f : c -> A, and we compare `f hc` vs `f h'` where hc, h'
    // are two distinct fvars of type c (a Prop). Proof irrelevance should fire.
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut tc = TypeChecker::new(&env);
    let a_const = Expr::const_(Name::from_string("A"), vec![]);

    // c : Prop  (a LOCAL fvar of type Prop)
    let c = tc
        .local_context_mut()
        .push(Name::from_string("c"), Expr::prop(), BinderInfo::Default);
    let c_e = Expr::from_kind(ExprKind::FVar(c));

    // f : c -> A
    let f = tc.local_context_mut().push(
        Name::from_string("f"),
        Expr::pi(BinderInfo::Default, c_e.clone(), a_const.clone()),
        BinderInfo::Default,
    );
    let f_e = Expr::from_kind(ExprKind::FVar(f));

    // hc : c, h2 : c  (two distinct proofs of the local Prop c)
    let hc = tc
        .local_context_mut()
        .push(Name::from_string("hc"), c_e.clone(), BinderInfo::Default);
    let h2 = tc
        .local_context_mut()
        .push(Name::from_string("h2"), c_e.clone(), BinderInfo::Default);

    let f_hc = Expr::app(f_e.clone(), Expr::from_kind(ExprKind::FVar(hc)));
    let f_h2 = Expr::app(f_e.clone(), Expr::from_kind(ExprKind::FVar(h2)));

    assert!(
        tc.is_def_eq(&f_hc, &f_h2),
        "f hc =?= f h2 with local Prop c must hold by proof irrelevance"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction test for indexed inductives with recursive fields (#1406).
//!
//! Verifies that `build_recursor_rule_rhs` inserts index arguments in the IH
//! call for indexed inductives. Vec.cons has `tail : Vec α n` (recursive field
//! in an indexed family); the IH must be `rec α motive minor_nil minor_cons n tail`
//! (with index `n`), not `rec α motive minor_nil minor_cons tail` (missing `n`).
//!
//! Also tests indexed+reflexive: IW (indexed W-type) where a higher-order
//! recursive field targets an indexed inductive, combining Pi-stripping with
//! index remapping in the IH lambda. Lean 4 ref: inductive.cpp:731-741.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Add Nat inductive to environment.
fn add_nat(env: &mut Environment) -> Expr {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat,
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
    .expect("add Nat");
    nat_ref
}

/// Add Vec inductive (indexed by Nat) to environment.
/// Uses Sort(succ u) for parameter and result (matching Lean 4's `Type u`)
/// so that the Nat index field (Sort(1)) satisfies is_geq(succ u, 1).
fn add_vec(env: &mut Environment, nat_ref: &Expr) -> Name {
    let u = Name::from_string("u");
    let vec_name = Name::from_string("Vec");
    let ulvl = Level::Param(u.clone());
    let succ_u = Level::succ(ulvl.clone());
    let vec_c = |lvls: Vec<Level>| Expr::const_(vec_name.clone(), lvls);

    // Vec : {α : Sort(succ u)} → Nat → Sort(succ u)
    let vec_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(succ_u.clone()),
        Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::sort(succ_u.clone()),
        ),
    );
    // nil : {α : Sort(succ u)} → Vec α Nat.zero
    let nil_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(succ_u.clone()),
        Expr::app(
            Expr::app(vec_c(vec![ulvl.clone()]), Expr::bvar(0)),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    // cons : {α : Sort(succ u)} → α → (n : Nat) → Vec α n → Vec α (succ n)
    let cons_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(succ_u.clone()),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(
                        Expr::app(vec_c(vec![ulvl.clone()]), Expr::bvar(2)),
                        Expr::bvar(0),
                    ),
                    Expr::app(
                        Expr::app(vec_c(vec![ulvl.clone()]), Expr::bvar(3)),
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.succ"), vec![]),
                            Expr::bvar(1),
                        ),
                    ),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: vec_name.clone(),
            type_: vec_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("Vec.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("Vec.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    })
    .expect("add Vec");
    vec_name
}

/// Build Nat + Vec environment. Returns (env, nat_ref, vec_name).
fn make_vec_env() -> (Environment, Expr, Name) {
    let mut env = Environment::new();
    let nat_ref = add_nat(&mut env);
    let vec_name = add_vec(&mut env, &nat_ref);
    (env, nat_ref, vec_name)
}

#[test]
fn test_vec_cons_recursor_metadata() {
    let (env, _, _) = make_vec_env();
    let rec_val = env
        .get_recursor(&Name::from_string("Vec.rec"))
        .expect("Vec.rec");
    assert_eq!(
        (rec_val.num_params, rec_val.num_indices, rec_val.num_minors),
        (1, 1, 2)
    );

    let cons_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("Vec.cons"))
        .expect("cons rule");
    assert_eq!(cons_rule.num_fields, 3);
    assert_eq!(cons_rule.recursive_fields, vec![false, false, true]);
    assert!(cons_rule.rhs.is_lam(), "cons rule RHS should be a lambda");
}

/// Vec.rec applied to cons must reduce with correct IH (including index).
#[test]
fn test_iota_reduction_indexed_recursive_field() {
    let (env, nat_ref, vec_name) = make_vec_env();
    let tc = TypeChecker::new(&env);
    let z = Level::zero();
    let one = Level::succ(z.clone()); // u=1: alpha=Type in Sort(2) accommodates Nat in Sort(1)
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let alpha = Expr::type_();
    let vc = |lvls| Expr::const_(vec_name.clone(), lvls);

    let nil = Expr::app(
        Expr::const_(Name::from_string("Vec.nil"), vec![one.clone()]),
        alpha.clone(),
    );
    let cons_val = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Vec.cons"), vec![one.clone()]),
                    alpha.clone(),
                ),
                Expr::prop(),
            ),
            zero.clone(),
        ),
        nil,
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(
                Expr::app(vc(vec![one.clone()]), alpha.clone()),
                Expr::bvar(0),
            ),
            Expr::prop(),
        ),
    );
    let minor_cons = Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref,
            Expr::lam(
                BinderInfo::Default,
                Expr::app(
                    Expr::app(vc(vec![one.clone()]), alpha.clone()),
                    Expr::bvar(0),
                ),
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
    );
    let succ_zero = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);
    // Vec.rec@{1,0} Type motive minor_nil minor_cons (succ zero) cons_val
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Vec.rec"), vec![one, z]),
                            alpha,
                        ),
                        motive,
                    ),
                    Expr::type_(),
                ),
                minor_cons,
            ),
            succ_zero,
        ),
        cons_val,
    );

    let result = tc.whnf(&app);
    assert_ne!(app, result, "Vec.rec (cons ...) must reduce");
    assert_eq!(result, Expr::prop(), "should reduce to Prop via minor_cons");
}

// === Indexed + Reflexive (IW type) tests ===
//
// IW : Nat → Type
// IW.mk : (n : Nat) → (f : Nat → IW n) → IW (Nat.succ n)
//
// This combines:
// - Indexed inductive (index = n : Nat in the IH call)
// - Reflexive field (f : Nat → IW n, higher-order recursive reference)
// The IH must be: λ x. IW.rec motive minor n (f x)
// With both index remapping AND lambda wrapping.

/// Add IW inductive (indexed W-type) to environment.
/// IW : Nat → Type with IW.mk : (n : Nat) → (f : Nat → IW n) → IW (Nat.succ n)
fn add_iw(env: &mut Environment, nat_ref: &Expr) -> Name {
    let iw_name = Name::from_string("IW");
    let iw_c = || Expr::const_(iw_name.clone(), vec![]);

    // IW : Nat → Type
    let iw_type = Expr::pi(BinderInfo::Default, nat_ref.clone(), Expr::type_());

    // IW.mk : (n : Nat) → (f : Nat → IW n) → IW (Nat.succ n)
    //
    // De Bruijn:
    //   Pi(Default, Nat,                                          -- n
    //     Pi(Default, Pi(Default, Nat, App(IW, BVar(1))),         -- f : Nat → IW n
    //       App(IW, App(Nat.succ, BVar(1)))))                     -- IW (succ n)
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(), // n : Nat
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(
                BinderInfo::Default,
                nat_ref.clone(),                  // x : Nat
                Expr::app(iw_c(), Expr::bvar(1)), // IW n (BVar(1)=n under x binder)
            ),
            Expr::app(
                iw_c(),
                Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::bvar(1), // n (BVar(0)=f, BVar(1)=n)
                ),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: iw_name.clone(),
            type_: iw_type,
            constructors: vec![Constructor {
                name: Name::from_string("IW.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("add IW");
    iw_name
}

/// Build Nat + IW environment. Returns (env, nat_ref, iw_name).
fn make_iw_env() -> (Environment, Expr, Name) {
    let mut env = Environment::new();
    let nat_ref = add_nat(&mut env);
    let iw_name = add_iw(&mut env, &nat_ref);
    (env, nat_ref, iw_name)
}

#[test]
fn test_iw_recursor_metadata() {
    let (env, _, _) = make_iw_env();
    let rec_val = env
        .get_recursor(&Name::from_string("IW.rec"))
        .expect("IW.rec");
    assert_eq!(
        (rec_val.num_params, rec_val.num_indices, rec_val.num_minors),
        (0, 1, 1),
        "IW has 0 params, 1 index, 1 constructor"
    );

    let mk_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("IW.mk"))
        .expect("mk rule");
    assert_eq!(mk_rule.num_fields, 2, "IW.mk has 2 fields: n and f");
    assert_eq!(
        mk_rule.recursive_fields,
        vec![false, true],
        "field[0]=n (non-rec), field[1]=f (recursive)"
    );
    assert!(mk_rule.rhs.is_lam(), "mk rule RHS should be a lambda");
}

/// Peel lambda binders from an expression, returning (body, count).
fn peel_lambdas(mut expr: Expr) -> (Expr, u32) {
    let mut count = 0u32;
    while let ExprKind::Lam(_, _, body) = expr.kind() {
        expr = (**body).clone();
        count += 1;
    }
    (expr, count)
}

/// Build constant IW minor: λ n f ih. Prop (ignores all args).
fn build_iw_const_minor(nat_ref: &Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::pi(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::app(Expr::const_(Name::from_string("IW"), vec![]), Expr::bvar(1)),
            ),
            Expr::lam(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, nat_ref.clone(), Expr::prop()),
                Expr::prop(),
            ),
        ),
    )
}

/// Verify the RHS lambda structure for IW.mk:
/// λ motive. λ minor. λ n. λ f. minor n f (λ x. IW.rec motive minor n (f x))
#[test]
fn test_iw_rhs_has_indexed_lambda_wrapped_ih() {
    let (env, _, _) = make_iw_env();
    let mk_rule = env
        .get_recursor(&Name::from_string("IW.rec"))
        .expect("IW.rec")
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("IW.mk"))
        .expect("mk rule")
        .clone();

    let (body, lam_count) = peel_lambdas(mk_rule.rhs.clone());
    assert_eq!(lam_count, 4, "RHS should have 4 lambda binders");

    // Body = App(App(App(minor, n), f), ih); peel outermost arg to get ih
    let ExprKind::App(_, ih) = body.kind() else {
        unreachable!("body should be App(..., ih), got: {:?}", body);
    };
    // IH must be a lambda (reflexive wrapping)
    let ExprKind::Lam(_, _, ih_body) = ih.kind() else {
        unreachable!("IH should be λ x. ..., not {:?}", ih);
    };
    // Under 5 binders: BVar(0)=x, BVar(1)=f, BVar(2)=n, BVar(3)=minor, BVar(4)=motive
    let ih_fn = ih_body.get_app_fn();
    let ih_args = ih_body.get_app_args();

    assert!(
        matches!(ih_fn.kind(), ExprKind::Const(n, _) if *n == Name::from_string("IW.rec")),
        "IH head should be IW.rec, got {:?}",
        ih_fn
    );
    assert_eq!(ih_args.len(), 4, "IH should have 4 args");
    assert_eq!(*ih_args[0].kind(), ExprKind::BVar(4), "arg 0 = motive");
    assert_eq!(*ih_args[1].kind(), ExprKind::BVar(3), "arg 1 = minor");
    assert_eq!(*ih_args[2].kind(), ExprKind::BVar(2), "arg 2 = index n");
    assert!(
        matches!(ih_args[3].kind(), ExprKind::App(f, x)
            if *f.kind() == ExprKind::BVar(1) && *x.kind() == ExprKind::BVar(0)),
        "arg 3 should be (f x), got {:?}",
        ih_args[3]
    );
}

/// IW.rec applied to (IW.mk n f) must reduce via indexed + lambda-wrapped IH.
#[test]
fn test_iota_reduction_indexed_reflexive() {
    let (env, nat_ref, _) = make_iw_env();
    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(Expr::const_(Name::from_string("IW"), vec![]), Expr::bvar(0)),
            Expr::prop(),
        ),
    );
    let minor = build_iw_const_minor(&nat_ref);
    let f_val = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::fvar(FVarId(42)),
    );
    let major = Expr::app(
        Expr::app(Expr::const_(Name::from_string("IW.mk"), vec![]), zero),
        f_val,
    );
    // IW.rec@{0} motive minor (succ zero) major
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("IW.rec"), vec![Level::zero()]),
                    motive,
                ),
                minor,
            ),
            succ_zero,
        ),
        major,
    );
    let result = tc.whnf(&app);
    assert_ne!(app, result, "IW.rec (IW.mk ...) must reduce");
    assert_eq!(
        result,
        Expr::prop(),
        "should reduce to Prop via constant minor"
    );
}

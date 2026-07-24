// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for structure eta expansion in definitional equality (basic cases).
//!
//! Structure eta: for a structure type S with single constructor S.mk and
//! projections s.0, s.1, ..., s.n, we have:
//!   s = S.mk (s.0) (s.1) ... (s.n)
//!
//! See also `struct_eta_advanced.rs` for parametric, Sigma, and predicate tests.
//!
//! Reference: Lean 4 kernel type_checker.cpp, inductive.cpp:98-111
//! Part of #3134

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

// --- Shared helpers (pub(super) so struct_eta_advanced can use them) ---

/// Build a simple structure with `n` fields all of type `field_ty`.
pub(super) fn build_simple_struct(
    env: &mut Environment,
    name: &str,
    num_fields: u32,
    field_ty: Expr,
    result_sort: Expr,
) {
    let struct_name = Name::from_string(name);
    let ctor_name = Name::from_string(&format!("{name}.mk"));

    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, field_ty.clone(), ctor_type);
    }

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name,
            type_: result_sort,
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    })
    .expect("add_inductive");
}

/// Build the eta expansion of `e` for a structure with no params.
pub(super) fn build_eta_expanded(
    struct_name: &Name,
    ctor_name: &Name,
    num_fields: u32,
    e: &Expr,
) -> Expr {
    let mut result = Expr::const_(ctor_name.clone(), vec![]);
    for i in 0..num_fields {
        result = Expr::app(result, Expr::proj(struct_name.clone(), i, e.clone()));
    }
    result
}

/// Build a Prod-like parametric pair: Prod : Type -> Type -> Type.
pub(super) fn setup_prod(env: &mut Environment) {
    let prod_name = Name::from_string("Prod");
    let prod_mk = Name::from_string("Prod.mk");

    let prod_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );

    // Prod.mk : (a : Type) -> (b : Type) -> a -> b -> Prod a b
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(Expr::const_(prod_name.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: prod_name,
            type_: prod_type,
            constructors: vec![Constructor {
                name: prod_mk,
                type_: mk_type,
            }],
        }],
    })
    .expect("add Prod");
}

/// Build `Prod.mk ty1 ty2 fld0 fld1`.
pub(super) fn build_prod_mk(ty1: &Expr, ty2: &Expr, fld0: Expr, fld1: Expr) -> Expr {
    let mut e = Expr::const_(Name::from_string("Prod.mk"), vec![]);
    e = Expr::app(e, ty1.clone());
    e = Expr::app(e, ty2.clone());
    e = Expr::app(e, fld0);
    e = Expr::app(e, fld1);
    e
}

/// Build `Prod.mk ty ty (Prod.proj 0 x) (Prod.proj 1 x)`.
pub(super) fn build_prod_eta(ty1: &Expr, ty2: &Expr, x: &Expr) -> Expr {
    let prod_name = Name::from_string("Prod");
    build_prod_mk(
        ty1,
        ty2,
        Expr::proj(prod_name.clone(), 0, x.clone()),
        Expr::proj(prod_name, 1, x.clone()),
    )
}

// --- Basic structure eta: simple non-parametric structs ---

/// s : S = S.mk (s.0) -- single-field structure
#[test]
fn test_struct_eta_single_field() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Wrap", 1, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let wrap_name = Name::from_string("Wrap");
    let s_id = tc.ctx.borrow_mut().push(
        Name::from_string("s"),
        Expr::const_(wrap_name.clone(), vec![]),
        BinderInfo::Default,
    );
    let s = Expr::fvar(s_id);
    let expanded = build_eta_expanded(&wrap_name, &Name::from_string("Wrap.mk"), 1, &s);

    assert!(tc.is_def_eq(&s, &expanded), "s = Wrap.mk (s.0)");
    assert!(tc.is_def_eq(&expanded, &s), "symmetric");
}

/// s : S = S.mk (s.0) (s.1) -- two-field structure
#[test]
fn test_struct_eta_two_fields() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Pair2", 2, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let name = Name::from_string("Pair2");
    let s_id = tc.ctx.borrow_mut().push(
        Name::from_string("s"),
        Expr::const_(name.clone(), vec![]),
        BinderInfo::Default,
    );
    let s = Expr::fvar(s_id);
    let expanded = build_eta_expanded(&name, &Name::from_string("Pair2.mk"), 2, &s);

    assert!(tc.is_def_eq(&s, &expanded), "s = Pair2.mk (s.0) (s.1)");
    assert!(tc.is_def_eq(&expanded, &s), "symmetric");
}

/// Distinct FVars of same struct type should NOT be def-eq.
#[test]
fn test_struct_eta_distinct_values_not_equal() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "W2", 2, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let w2_ty = Expr::const_(Name::from_string("W2"), vec![]);
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        w2_ty.clone(),
        BinderInfo::Default,
    ));
    let b = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("b"),
        w2_ty,
        BinderInfo::Default,
    ));
    assert!(!tc.is_def_eq(&a, &b), "distinct FVars not def-eq");
}

// --- Parametric Prod eta ---

/// p : Prod Nat Nat = Prod.mk Nat Nat (p.0) (p.1)
#[test]
fn test_struct_eta_prod_nat_nat() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prod_nat_nat = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Prod"), vec![]), nat.clone()),
        nat.clone(),
    );

    let p_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("p"), prod_nat_nat, BinderInfo::Default);
    let p = Expr::fvar(p_id);
    let expanded = build_prod_eta(&nat, &nat, &p);

    assert!(
        tc.is_def_eq(&p, &expanded),
        "p = Prod.mk Nat Nat (p.0) (p.1)"
    );
    assert!(tc.is_def_eq(&expanded, &p), "symmetric");
}

/// Identical constructor applications should be def-eq.
#[test]
fn test_struct_eta_ctor_app_identity() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        nat.clone(),
        BinderInfo::Default,
    ));
    let b = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("b"),
        nat.clone(),
        BinderInfo::Default,
    ));

    let mk1 = build_prod_mk(&nat, &nat, a.clone(), b.clone());
    let mk2 = build_prod_mk(&nat, &nat, a, b);
    assert!(tc.is_def_eq(&mk1, &mk2), "identical ctor apps def-eq");
}

/// Prod.mk Nat Nat (p.0) (p.1) = p (canonical structure eta example)
#[test]
fn test_struct_eta_ctor_vs_fvar() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prod_nat_nat = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Prod"), vec![]), nat.clone()),
        nat.clone(),
    );
    let p = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("p"),
        prod_nat_nat,
        BinderInfo::Default,
    ));
    let expanded = build_prod_eta(&nat, &nat, &p);
    assert!(tc.is_def_eq(&expanded, &p), "Prod.mk ... (p.0) (p.1) = p");
}

/// Two eta-expansions of the same FVar should be def-eq.
#[test]
fn test_struct_eta_both_sides_expanded() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prod_nat_nat = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Prod"), vec![]), nat.clone()),
        nat.clone(),
    );
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        prod_nat_nat,
        BinderInfo::Default,
    ));

    let exp1 = build_prod_eta(&nat, &nat, &a);
    let exp2 = build_prod_eta(&nat, &nat, &a);
    assert!(
        tc.is_def_eq(&exp1, &exp2),
        "two eta-expansions of same FVar def-eq"
    );
}

// --- Unit-like / zero-field structure ---

/// All values of a unit-like type are def-eq (is_def_eq_unit_like).
#[test]
fn test_struct_eta_unit_like() {
    let mut env = Environment::new();
    let unit_name = Name::from_string("MyUnit");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: unit_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("MyUnit.mk"),
                type_: Expr::const_(unit_name.clone(), vec![]),
            }],
        }],
    })
    .expect("add MyUnit");

    let tc = TypeChecker::new(&env);
    let ty = Expr::const_(unit_name, vec![]);
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        ty.clone(),
        BinderInfo::Default,
    ));
    let b = Expr::fvar(
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("b"), ty, BinderInfo::Default),
    );
    assert!(tc.is_def_eq(&a, &b), "two values of unit-like type def-eq");
}

// --- Nested structures ---

/// o : Outer = Outer.mk (o.0) and o.0 = Inner.mk (o.0.0) (o.0.1)
#[test]
fn test_struct_eta_nested_outer() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Inner", 2, nat, Expr::type_());

    let inner_ty = Expr::const_(Name::from_string("Inner"), vec![]);
    let outer_name = Name::from_string("Outer");
    let outer_mk = Name::from_string("Outer.mk");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: outer_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: outer_mk.clone(),
                type_: Expr::pi(
                    BinderInfo::Default,
                    inner_ty,
                    Expr::const_(outer_name.clone(), vec![]),
                ),
            }],
        }],
    })
    .expect("add Outer");

    let tc = TypeChecker::new(&env);
    let o = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("o"),
        Expr::const_(outer_name.clone(), vec![]),
        BinderInfo::Default,
    ));

    let o_expanded = Expr::app(
        Expr::const_(outer_mk, vec![]),
        Expr::proj(outer_name.clone(), 0, o.clone()),
    );
    assert!(tc.is_def_eq(&o, &o_expanded), "o = Outer.mk (o.0)");
}

/// Inner eta through a projection: o.0 = Inner.mk (o.0.0) (o.0.1)
#[test]
fn test_struct_eta_nested_inner() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Inner", 2, nat, Expr::type_());

    let inner_ty = Expr::const_(Name::from_string("Inner"), vec![]);
    let outer_name = Name::from_string("Outer");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: outer_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Outer.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    inner_ty,
                    Expr::const_(outer_name.clone(), vec![]),
                ),
            }],
        }],
    })
    .expect("add Outer");

    let tc = TypeChecker::new(&env);
    let o = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("o"),
        Expr::const_(outer_name.clone(), vec![]),
        BinderInfo::Default,
    ));

    let o_inner = Expr::proj(outer_name, 0, o);
    let inner_name = Name::from_string("Inner");
    let inner_expanded = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Inner.mk"), vec![]),
            Expr::proj(inner_name.clone(), 0, o_inner.clone()),
        ),
        Expr::proj(inner_name, 1, o_inner.clone()),
    );
    assert!(
        tc.is_def_eq(&o_inner, &inner_expanded),
        "o.0 = Inner.mk (o.0.0) (o.0.1)"
    );
}

// --- Concrete field values and projection reduction ---

/// Prod.mk Nat Nat 1 2 reflexively def-eq.
#[test]
fn test_struct_eta_literal_fields_reflexive() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pair = build_prod_mk(&nat, &nat, Expr::nat_lit(1), Expr::nat_lit(2));
    assert!(tc.is_def_eq(&pair, &pair), "reflexive");
}

/// Prod.mk Nat Nat 1 2 != Prod.mk Nat Nat 1 3.
#[test]
fn test_struct_eta_different_fields_not_equal() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let p1 = build_prod_mk(&nat, &nat, Expr::nat_lit(1), Expr::nat_lit(2));
    let p2 = build_prod_mk(&nat, &nat, Expr::nat_lit(1), Expr::nat_lit(3));
    assert!(!tc.is_def_eq(&p1, &p2), "different fields not def-eq");
}

/// (Prod.mk Nat Nat a b).0 reduces to a, .1 to b.
#[test]
fn test_struct_eta_projection_reduces_ctor() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        nat.clone(),
        BinderInfo::Default,
    ));
    let b = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("b"),
        nat.clone(),
        BinderInfo::Default,
    ));

    let mk = build_prod_mk(&nat, &nat, a.clone(), b.clone());
    let prod_name = Name::from_string("Prod");
    assert!(
        tc.is_def_eq(&Expr::proj(prod_name.clone(), 0, mk.clone()), &a),
        "(mk a b).0 = a"
    );
    assert!(
        tc.is_def_eq(&Expr::proj(prod_name, 1, mk), &b),
        "(mk a b).1 = b"
    );
}

/// 16-field structure stress test for batch projection cache.
#[test]
fn test_struct_eta_16_fields() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "S16", 16, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let s16_name = Name::from_string("S16");
    let x = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("x"),
        Expr::const_(s16_name.clone(), vec![]),
        BinderInfo::Default,
    ));
    let expanded = build_eta_expanded(&s16_name, &Name::from_string("S16.mk"), 16, &x);

    assert!(tc.is_def_eq(&x, &expanded), "x = S16.mk (x.0) ... (x.15)");
    assert!(tc.is_def_eq(&expanded, &x), "symmetric");
}

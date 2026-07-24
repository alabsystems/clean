// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Coq template-inductive cumulativity (`is_le_template_inductive`),
//! the last rung of the prod-poly program. The rule accepts
//! `prod.{0,0} A B ≤ prod.{1,1} A B` (same args, pointwise `≤` universe
//! instances) and is otherwise strictly conservative.

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn nm(s: &str) -> Name {
    Name::from_string(s)
}

/// `Sort 0` (Prop) — a valid argument for BOTH `prod.{0,0}` and `prod.{1,1}`
/// (by sort cumulativity `A : Prop ⇒ A : Type`).
fn prop() -> Expr {
    Expr::sort(Level::zero())
}

/// `prod.{lu,lv} lhs rhs`.
fn prod_app(lu: Level, lv: Level, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(nm("tpl.prod"), vec![lu, lv]), [lhs, rhs])
}

fn lvl0() -> Level {
    Level::zero()
}
fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// Register the template-polymorphic singleton `prod`, the 2-constructor
/// `esum` (a NON-singleton control), the single-ctor non-parametric-field
/// `endo` (a condition-4 control), and the arg axioms `A`, `B`, `C : Prop`.
fn env_with_template_inductives() -> Environment {
    let mut env = Environment::new();
    let u = Level::param(nm("u"));
    let v = Level::param(nm("v"));
    let sort_u = Expr::sort(u.clone());
    let sort_v = Expr::sort(v.clone());
    let sort_max = Expr::sort(Level::max(u.clone(), v.clone()));

    // prod : Π (Sort u) (Sort v). Sort (max u v)
    let prod_arity = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, sort_v.clone(), sort_max.clone()),
    );
    // pair : (A : Sort u)(B : Sort v)(a : A)(b : B) → prod.{u,v} A B
    let prod_uv = Expr::const_(nm("tpl.prod"), vec![u.clone(), v.clone()]);
    let prod_result = Expr::apps(prod_uv, [Expr::bvar(3), Expr::bvar(2)]);
    let pair_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort_v.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    prod_result,
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![nm("u"), nm("v")],
        num_params: 2,
        types: vec![InductiveType {
            name: nm("tpl.prod"),
            type_: prod_arity,
            constructors: vec![Constructor {
                name: nm("tpl.prod.mk"),
                type_: pair_ty,
            }],
        }],
    })
    .expect("template-poly prod should register");

    // esum : Π (Sort u)(Sort v). Sort (max u v), TWO constructors (inl/inr).
    let esum_arity = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, sort_v.clone(), sort_max.clone()),
    );
    let esum_uv = Expr::const_(nm("tpl.esum"), vec![u.clone(), v.clone()]);
    // inl : (A : Sort u)(B : Sort v)(a : A) → esum A B
    let inl_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort_v.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::apps(esum_uv.clone(), [Expr::bvar(2), Expr::bvar(1)]),
            ),
        ),
    );
    // inr : (A : Sort u)(B : Sort v)(b : B) → esum A B
    let inr_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort_v.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0), // b : B
                Expr::apps(esum_uv, [Expr::bvar(2), Expr::bvar(1)]),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![nm("u"), nm("v")],
        num_params: 2,
        types: vec![InductiveType {
            name: nm("tpl.esum"),
            type_: esum_arity,
            constructors: vec![
                Constructor {
                    name: nm("tpl.esum.inl"),
                    type_: inl_ty,
                },
                Constructor {
                    name: nm("tpl.esum.inr"),
                    type_: inr_ty,
                },
            ],
        }],
    })
    .expect("2-constructor esum should register");

    // endo : Π (Sort u). Sort u, single ctor whose field is `A → A` (NOT a bare
    // BVar) — the condition-4 control.
    let endo_arity = Expr::pi(BinderInfo::Default, sort_u.clone(), sort_u.clone());
    let endo_u = Expr::const_(nm("tpl.endo"), vec![u.clone()]);
    // mk : (A : Sort u)(f : A → A) → endo A
    let endo_mk_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::arrow(Expr::bvar(0), Expr::bvar(1)), // f : A → A (a Pi, not a BVar)
            Expr::app(endo_u, Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![nm("u")],
        num_params: 1,
        types: vec![InductiveType {
            name: nm("tpl.endo"),
            type_: endo_arity,
            constructors: vec![Constructor {
                name: nm("tpl.endo.mk"),
                type_: endo_mk_ty,
            }],
        }],
    })
    .expect("single-ctor endo should register");

    for a in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: nm(a),
            level_params: vec![],
            type_: prop(),
        })
        .unwrap_or_else(|e| panic!("axiom {a} : Prop should register: {e:?}"));
    }
    env
}

fn cumulative_tc(env: &Environment) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(env);
    tc.set_cumulative(true);
    tc
}

// ── Positive: the real_maxrN shape ──────────────────────────────────────────

#[test]
fn test_template_cumul_prod_prop_le_type_same_args() {
    // THE landing case: prod.{0,0} A B ≤ prod.{1,1} A B (identical args).
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let lhs = prod_app(
        lvl0(),
        lvl0(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    let rhs = prod_app(
        lvl1(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    assert!(
        tc.is_le(&lhs, &rhs),
        "prod.{{0,0}} A B ≤ prod.{{1,1}} A B must hold (template cumulativity)"
    );
}

#[test]
fn test_template_cumul_prod_mixed_pointwise_le() {
    // Pointwise, per-parameter: {0,1} ≤ {1,1} (0≤1 and 1≤1).
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let lhs = prod_app(
        lvl0(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    let rhs = prod_app(
        lvl1(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    assert!(
        tc.is_le(&lhs, &rhs),
        "prod.{{0,1}} A B ≤ prod.{{1,1}} A B must hold"
    );
}

#[test]
fn test_template_cumul_prod_reflexive_instance() {
    // Same instance is accepted (via is_def_eq — sanity, not the new rule).
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let e = prod_app(
        lvl1(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    assert!(tc.is_le(&e, &e), "prod.{{1,1}} A B ≤ itself");
}

// ── Negative controls ───────────────────────────────────────────────────────

#[test]
fn test_template_cumul_rejects_non_pointwise_le_levels() {
    // 1 ≤ 0 is FALSE, so the DOWNWARD direction must be rejected.
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let hi = prod_app(
        lvl1(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    let lo = prod_app(
        lvl0(),
        lvl0(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    assert!(
        !tc.is_le(&hi, &lo),
        "prod.{{1,1}} A B ≤ prod.{{0,0}} A B must be REJECTED (1 ≰ 0)"
    );
}

#[test]
fn test_template_cumul_rejects_different_args() {
    // Invariant parameters: distinct args are never subtyped.
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let lhs = prod_app(
        lvl0(),
        lvl0(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    let rhs = prod_app(
        lvl1(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("C"), vec![]),
    );
    assert!(
        !tc.is_le(&lhs, &rhs),
        "prod.{{0,0}} A B ≤ prod.{{1,1}} A C must be REJECTED (B ≠ C)"
    );
}

#[test]
fn test_template_cumul_rejects_two_constructor_inductive() {
    // esum has TWO constructors ⇒ NOT a template-poly singleton ⇒ the rule is
    // conservative and rejects it (the "non-template inductive" control).
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let lhs = Expr::apps(
        Expr::const_(nm("tpl.esum"), vec![lvl0(), lvl0()]),
        [Expr::const_(nm("A"), vec![]), Expr::const_(nm("B"), vec![])],
    );
    let rhs = Expr::apps(
        Expr::const_(nm("tpl.esum"), vec![lvl1(), lvl1()]),
        [Expr::const_(nm("A"), vec![]), Expr::const_(nm("B"), vec![])],
    );
    assert!(
        !tc.is_le(&lhs, &rhs),
        "esum.{{0,0}} A B ≤ esum.{{1,1}} A B must be REJECTED (2 constructors)"
    );
}

#[test]
fn test_template_cumul_rejects_non_parametric_field() {
    // endo's single field is `A → A` (a Pi, not a bare BVar) ⇒ condition 4 fails
    // ⇒ rejected. This guards against a universe parameter appearing in a field.
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let lhs = Expr::app(
        Expr::const_(nm("tpl.endo"), vec![lvl0()]),
        Expr::const_(nm("A"), vec![]),
    );
    let rhs = Expr::app(
        Expr::const_(nm("tpl.endo"), vec![lvl1()]),
        Expr::const_(nm("A"), vec![]),
    );
    assert!(
        !tc.is_le(&lhs, &rhs),
        "endo.{{0}} A ≤ endo.{{1}} A must be REJECTED (field is not a bare BVar)"
    );
}

#[test]
fn test_template_cumul_rejects_different_heads() {
    // Different inductive heads are never related.
    let env = env_with_template_inductives();
    let tc = cumulative_tc(&env);
    let lhs = prod_app(
        lvl0(),
        lvl0(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    let rhs = Expr::apps(
        Expr::const_(nm("tpl.esum"), vec![lvl1(), lvl1()]),
        [Expr::const_(nm("A"), vec![]), Expr::const_(nm("B"), vec![])],
    );
    assert!(
        !tc.is_le(&lhs, &rhs),
        "prod ≤ esum must be REJECTED (different heads)"
    );
}

// ── The Lean-lane control: the rule is inert without cumulativity ────────────

#[test]
fn test_template_cumul_inert_in_non_cumulative_lean_lane() {
    // A default (non-cumulative) checker is the Lean lane: `is_le` collapses to
    // `is_def_eq`, and prod.{0,0} A B is NOT def-eq to prod.{1,1} A B.
    let env = env_with_template_inductives();
    let tc = TypeChecker::new(&env); // cumulative == false (default)
    assert!(
        !tc.is_cumulative(),
        "default checker must be non-cumulative (Lean lane)"
    );
    let lhs = prod_app(
        lvl0(),
        lvl0(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    let rhs = prod_app(
        lvl1(),
        lvl1(),
        Expr::const_(nm("A"), vec![]),
        Expr::const_(nm("B"), vec![]),
    );
    assert!(
        !tc.is_le(&lhs, &rhs),
        "template cumulativity MUST NOT fire in the non-cumulative Lean lane"
    );
    // And the direct call is inert too (defense-in-depth guard).
    assert!(
        !tc.is_le_template_inductive(&lhs, &rhs),
        "is_le_template_inductive must return false when !cumulative"
    );
}

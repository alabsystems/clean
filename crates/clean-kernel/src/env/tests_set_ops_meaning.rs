// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the twelve `Set` operations MEAN (KR1 increment 3, `docs/DECISIONS.md`
//! R143). The prelude ratchet only counts that they stopped being axioms; a
//! body with the wrong connective (`Set.union := s a ∧ t a`, `Set.empty :=
//! True`) kept every other test green in review. Each operation, applied to
//! opaque predicates `P`, `Q : Nat → Prop` and points `a`, `x : Nat`, must be
//! definitionally Mathlib's pointwise predicate, and must NOT be
//! definitionally a neighbouring wrong one (the control that the comparison
//! discriminates at all).

use super::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use crate::Declaration;

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

/// `Set.<op>.{0}` applied to `Nat` and `args`.
fn op(name: &str, args: &[Expr]) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        std::iter::once(c("Nat")).chain(args.iter().cloned()),
    )
}

fn bin(name: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(c(name), [a, b])
}

fn not(a: Expr) -> Expr {
    Expr::app(c("Not"), a)
}

fn eq_nat(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), a, b],
    )
}

fn env_with_points() -> Environment {
    let mut env = Environment::with_prelude();
    let pred = Expr::pi(BinderInfo::Default, c("Nat"), Expr::prop());
    for (n, ty) in [
        ("kr3_P", pred.clone()),
        ("kr3_Q", pred),
        ("kr3_a", c("Nat")),
        ("kr3_x", c("Nat")),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: ty,
        })
        .expect("test point");
    }
    env
}

#[test]
fn test_every_set_operation_is_its_pointwise_predicate() {
    let env = env_with_points();
    let tc = TypeChecker::new(&env);
    let (p, q, a, x) = (c("kr3_P"), c("kr3_Q"), c("kr3_a"), c("kr3_x"));
    let pa = Expr::app(p.clone(), a.clone());
    let qa = Expr::app(q.clone(), a.clone());
    // (operation applied, its meaning, a wrong meaning it must not have)
    let cases: Vec<(&str, Expr, Expr, Expr)> = vec![
        (
            "Set.mem",
            op("Set.mem", &[p.clone(), a.clone()]),
            pa.clone(),
            qa.clone(),
        ),
        (
            "setOf",
            Expr::app(op("setOf", std::slice::from_ref(&p)), a.clone()),
            pa.clone(),
            qa.clone(),
        ),
        (
            "Set.union",
            op("Set.union", &[p.clone(), q.clone(), a.clone()]),
            bin("Or", pa.clone(), qa.clone()),
            bin("And", pa.clone(), qa.clone()),
        ),
        (
            "Set.inter",
            op("Set.inter", &[p.clone(), q.clone(), a.clone()]),
            bin("And", pa.clone(), qa.clone()),
            bin("Or", pa.clone(), qa.clone()),
        ),
        (
            "Set.diff",
            op("Set.diff", &[p.clone(), q.clone(), a.clone()]),
            bin("And", pa.clone(), not(qa.clone())),
            bin("And", qa.clone(), not(pa.clone())),
        ),
        (
            "Set.symmDiff",
            op("Set.symmDiff", &[p.clone(), q.clone(), a.clone()]),
            bin(
                "Or",
                bin("And", pa.clone(), not(qa.clone())),
                bin("And", qa.clone(), not(pa.clone())),
            ),
            bin("And", pa.clone(), not(qa.clone())),
        ),
        (
            "Set.compl",
            op("Set.compl", &[p.clone(), a.clone()]),
            not(pa.clone()),
            pa.clone(),
        ),
        (
            "Set.empty",
            op("Set.empty", std::slice::from_ref(&a)),
            c("False"),
            c("True"),
        ),
        (
            "Set.univ",
            op("Set.univ", std::slice::from_ref(&a)),
            c("True"),
            c("False"),
        ),
        (
            "Set.singleton",
            op("Set.singleton", &[x.clone(), a.clone()]),
            eq_nat(a.clone(), x.clone()),
            eq_nat(a.clone(), a.clone()),
        ),
        (
            "Set.insert",
            op("Set.insert", &[x.clone(), p.clone(), a.clone()]),
            bin("Or", eq_nat(a.clone(), x.clone()), pa.clone()),
            bin("And", eq_nat(a.clone(), x.clone()), pa.clone()),
        ),
        (
            "Set.Subset",
            op("Set.Subset", &[p.clone(), q.clone()]),
            Expr::pi(
                BinderInfo::StrictImplicit,
                c("Nat"),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(p.clone(), Expr::bvar(0)),
                    Expr::app(q.clone(), Expr::bvar(1)),
                ),
            ),
            Expr::pi(
                BinderInfo::StrictImplicit,
                c("Nat"),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(q, Expr::bvar(0)),
                    Expr::app(p, Expr::bvar(1)),
                ),
            ),
        ),
    ];
    assert_eq!(cases.len(), 12, "one case per operation");
    for (name, applied, meaning, wrong) in cases {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} is declared"));
        assert!(info.value.is_some(), "{name} is a definition");
        assert!(
            tc.is_def_eq(&applied, &meaning),
            "{name} unfolds to its pointwise predicate"
        );
        assert!(
            !tc.is_def_eq(&applied, &wrong),
            "control: {name} is not the neighbouring wrong predicate"
        );
    }
}

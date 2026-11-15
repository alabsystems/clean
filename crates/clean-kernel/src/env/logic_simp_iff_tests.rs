// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G39's prelude theorems: present, kernel-checked, Lean's telescope, and the
//! advertised axiom closure.

use super::*;
use crate::env::ConstantKind;
use crate::expr::ExprKind;
use crate::TypeChecker;

const NAMES: [&str; 10] = [
    "ite_eq_left_iff",
    "ite_eq_right_iff",
    "imp_false",
    "Decidable.not_not",
    "not_false_eq_true",
    "not_true_eq_false",
    "forall_congr",
    "implies_true",
    "false_implies",
    "ne_eq",
];

#[test]
fn test_simp_logic_iff_lemmas_are_theorems_in_the_prelude() {
    let env = Environment::with_prelude();
    for name in NAMES {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must resolve in the default prelude env"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} is a theorem");
        let proof = info.value.as_ref().expect("a theorem has a proof");
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(proof).expect("proof type checks");
        assert!(tc.is_def_eq(&inferred, &info.type_), "{name}");
    }
}

/// Prevent a prelude/import collision from narrowing Lean's polymorphic
/// `implies_true` or widening the proposition-only `false_implies`.
#[test]
fn test_implication_true_telescope_matches_lean() {
    let env = Environment::with_prelude();
    let u = Name::from_string("u");
    let prop = Expr::sort(Level::zero());
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let true_ = konst("True");
    for (name, binder, lhs, levels) in [
        (
            "implies_true",
            Expr::sort(Level::param(u.clone())),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), true_.clone()),
            vec![u],
        ),
        (
            "false_implies",
            prop.clone(),
            Expr::pi(BinderInfo::Default, konst("False"), Expr::bvar(1)),
            vec![],
        ),
    ] {
        let info = env.get_const(&Name::from_string(name)).expect("registered");
        let expected = Expr::pi(
            BinderInfo::Default,
            binder,
            Expr::apps(eq.clone(), [prop.clone(), lhs, true_.clone()]),
        );
        assert_eq!(info.type_, expected, "{name}");
        assert_eq!(info.level_params, levels, "{name}");
    }
}

#[test]
fn test_simp_logic_iff_lemmas_axiom_closure() {
    let env = Environment::with_prelude();
    for name in NAMES {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .expect("registered");
        let names: Vec<String> = deps.iter().map(ToString::to_string).collect();
        let allowed: &[&str] = if matches!(
            name,
            "forall_congr"
                | "not_false_eq_true"
                | "not_true_eq_false"
                | "implies_true"
                | "false_implies"
        ) {
            &["propext"]
        } else {
            &[]
        };
        for d in &names {
            assert!(
                allowed.contains(&d.as_str()),
                "{name} axiom closure must be ⊆ {allowed:?}, found {d} (full {names:?})"
            );
        }
    }
}

/// Idempotent, and a second registration never replaces the first.
#[test]
fn test_simp_logic_iff_lemmas_registration_is_idempotent() {
    let mut env = Environment::with_prelude();
    env.register_simp_logic_iff_lemmas().expect("again");
    env.register_simp_logic_iff_lemmas().expect("and again");
}

/// Lean v4.30.0-rc2's binder telescope (pinned `#check @ite_eq_left_iff`):
/// `{α} {p} [inst] {x y}`, then the `Iff` — the spelling `.olean` import
/// would otherwise be shadowed by. A different telescope would mis-slot
/// `@ite_eq_left_iff α p inst x y` written against Lean.
#[test]
fn test_ite_eq_iff_telescope_matches_lean() {
    let env = Environment::with_prelude();
    for name in ["ite_eq_left_iff", "ite_eq_right_iff"] {
        let mut ty = env
            .get_const(&Name::from_string(name))
            .expect("registered")
            .type_
            .clone();
        let mut infos = Vec::new();
        while let ExprKind::Pi(bi, _, body) = ty.kind() {
            infos.push(bi.info);
            let next = body.as_ref().clone();
            ty = next;
        }
        assert_eq!(
            infos,
            vec![
                BinderInfo::Implicit,
                BinderInfo::Implicit,
                BinderInfo::InstImplicit,
                BinderInfo::Implicit,
                BinderInfo::Implicit,
            ],
            "{name}"
        );
        assert!(
            matches!(ty.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Iff")),
            "{name} concludes in Iff"
        );
    }
}

/// Pinned Lean (4.8.0 and v4.30.0-rc2) `#check @ne_eq`:
/// `∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b`, axiom-free.
#[test]
fn test_ne_eq_telescope_matches_lean() {
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("ne_eq"))
        .expect("registered");
    assert_eq!(info.level_params, vec![Name::from_string("u_1")]);
    let mut ty = info.type_.clone();
    let mut infos = Vec::new();
    while let ExprKind::Pi(bi, _, body) = ty.kind() {
        infos.push(bi.info);
        let next = body.as_ref().clone();
        ty = next;
    }
    assert_eq!(
        infos,
        vec![
            BinderInfo::Implicit,
            BinderInfo::Default,
            BinderInfo::Default
        ]
    );
    let args = ty.get_app_args();
    assert_eq!(args.len(), 3, "an `Eq` over `Prop`");
    let head_is = |e: &Expr, name: &str| matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string(name));
    assert!(head_is(args[1], "Ne"), "lhs is `a ≠ b`");
    assert!(head_is(args[2], "Not"), "rhs is `¬(a = b)`");
}

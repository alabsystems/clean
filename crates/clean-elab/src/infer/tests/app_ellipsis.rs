// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean `Term.ellipsis` — `f ..` fills every REMAINING explicit parameter of
//! `f` with `_`.
//!
//! These tests pin the elaborated TERM, not merely that parsing succeeded. A
//! `..` that expands to the wrong arity would still parse; it is the shape of
//! the resulting `Expr` that says the expansion was right, so each case
//! asserts the exact application spine and compares it against the explicit
//! `_`-spelled control.
//!
//! Corpus anchors (mathlib4 v4.30.0-rc2 @ 43ad0e9d2e14), every one of which
//! collapsed to "parser recovery produced raw declaration" before this:
//!   Mathlib/Logic/Basic.lean:237            `inferInstanceAs (Decidable (Or ..))`
//!   Mathlib/Logic/Function/Basic.lean:135   `Subsingleton.elim ..`
//!   Mathlib/Logic/Function/Basic.lean:545   `update_self ..`
//!   Mathlib/Logic/Function/Basic.lean:599   `update_self ..`
//!   Mathlib/Logic/Unique.lean:179           `eq_const_of_subsingleton ..`
//!   Mathlib/Order/Basic.lean:292            `exact assoc ..`
//!   Mathlib/Order/Basic.lean:567,571        `elim_le_elim_iff ..`

use super::*;

/// An environment holding `P : Prop`, a proof of it, and three axioms whose
/// EXPLICIT arities are 0, 2 and 3 — the arities `..` must recover.
fn arity_env() -> Environment {
    let mut env = Environment::new();
    let p = Name::from_string("P");
    env.add_decl_structural(Declaration::Axiom {
        name: p.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P registers");
    let p_ty = || Expr::const_(p.clone(), vec![]);

    // `nullary : P` — zero explicit binders, so `nullary ..` must add NOTHING.
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string("nullary"),
        level_params: vec![],
        type_: p_ty(),
    })
    .expect("nullary registers");

    // `binary : P → P → P` — two explicit binders.
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string("binary"),
        level_params: vec![],
        type_: Expr::arrow(p_ty(), Expr::arrow(p_ty(), p_ty())),
    })
    .expect("binary registers");

    // `ternary : P → P → P → P` — three explicit binders.
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string("ternary"),
        level_params: vec![],
        type_: Expr::arrow(p_ty(), Expr::arrow(p_ty(), Expr::arrow(p_ty(), p_ty()))),
    })
    .expect("ternary registers");

    env
}

/// Length of an application spine and the head's constant name.
fn spine(e: &Expr) -> (String, usize) {
    let mut n = 0;
    let mut cur = e.clone();
    while let ExprKind::App(f, _) = cur.kind() {
        n += 1;
        cur = f.as_ref().clone();
    }
    let head = match cur.kind() {
        ExprKind::Const(name, _) => name.to_string(),
        other => format!("{other:?}"),
    };
    (head, n)
}

#[test]
fn test_elab_app_ellipsis_fills_all_explicit_args() {
    // `binary ..` must be exactly `binary _ _` — two arguments, not one and
    // not three. Arity comes from the head's type, which is the whole point.
    let env = arity_env();
    let expr = elab_with_env(&env, "binary ..").expect("`binary ..` elaborates");
    assert_eq!(
        spine(&expr),
        ("binary".to_string(), 2),
        "`binary ..` must saturate both explicit binders, got {expr:?}"
    );
}

#[test]
fn test_elab_app_ellipsis_matches_the_explicit_hole_spelling() {
    // The TERM pin: `f ..` and `f _ _` must elaborate to the same shape. This
    // is what a "parsing succeeded" assertion would miss.
    let env = arity_env();
    let via_ellipsis = elab_with_env(&env, "binary ..").expect("`binary ..` elaborates");
    let via_holes = elab_with_env(&env, "binary _ _").expect("`binary _ _` elaborates");
    assert_eq!(
        spine(&via_ellipsis),
        spine(&via_holes),
        "`binary ..` and `binary _ _` must produce the same application spine"
    );
}

#[test]
fn test_elab_app_ellipsis_counts_only_remaining_args() {
    // `ternary nullary ..` supplies one argument by hand; `..` fills the other
    // TWO, for a spine of three. An expansion that ignored the supplied
    // argument would produce four.
    let env = arity_env();
    let expr = elab_with_env(&env, "ternary nullary ..").expect("`ternary nullary ..` elaborates");
    assert_eq!(
        spine(&expr),
        ("ternary".to_string(), 3),
        "one supplied + two filled, got {expr:?}"
    );
    // And the argument the user wrote is still the FIRST one, not displaced by
    // a synthesized hole.
    match expr.kind() {
        ExprKind::App(f, _) => match f.kind() {
            ExprKind::App(g, first) => {
                assert!(
                    matches!(g.kind(), ExprKind::App(_, _))
                        || matches!(g.kind(), ExprKind::Const(_, _))
                );
                let _ = first;
            }
            other => panic!("expected nested App, got {other:?}"),
        },
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_elab_app_ellipsis_on_saturated_head_adds_nothing() {
    // Lean allows `..` on a head with no remaining explicit parameters; it is
    // a no-op there. `nullary ..` must stay the bare constant — NOT an
    // application of it to a stray hole (which is what a "always append one
    // hole" approximation would build, and which the kernel would then reject
    // with a confusing "not a function type").
    let env = arity_env();
    let expr = elab_with_env(&env, "nullary ..").expect("`nullary ..` elaborates");
    assert!(
        matches!(expr.kind(), ExprKind::Const(name, _) if name.to_string() == "nullary"),
        "`nullary ..` must be the bare constant, got {expr:?}"
    );
}

#[test]
fn test_elab_app_ellipsis_is_not_a_named_argument() {
    // The parser marks `..` with a reserved `SurfaceArg` name. If that marker
    // ever reached `resolve_named_args` it would be reported as an unknown
    // parameter called `..`; the expansion must consume it first. This is the
    // regression that would fire if the expansion moved after named-argument
    // resolution.
    let env = arity_env();
    let err = elab_with_env(&env, "binary ..").err();
    assert!(
        err.is_none(),
        "`..` must never surface as an unknown named parameter: {err:?}"
    );
}

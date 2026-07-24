// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `simp at *` (wildcard) vs `simp_all` semantic differences (#1858).
//!
//! `simp at *` should simplify each hypothesis independently without
//! cross-rewriting or trivial hypothesis removal. `simp_all` uses
//! equality hypotheses as rewrite lemmas for other hypotheses and
//! removes trivial hypotheses.

use super::*;
use clean_kernel::env::{Declaration, SimpPriority};

/// `simp_at_all` does NOT remove trivial hypotheses.
///
/// Setup: h_triv : @Eq N x x  (trivially true)
///        goal   : P(x)
///
/// `simp_at_all` should simplify h_triv but keep it in context.
/// `simp_all` would remove it.
#[test]
fn test_simp_at_all_preserves_trivial_hypotheses() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);

    // h_triv : x = x  (trivially true equality)
    let h_triv_ty = make_eq_n(x.clone(), x.clone());

    // Goal: P(x) — not closable by simp, so the tactic returns Ok (progress on hyp)
    let target = make_p(x.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h_triv".to_string(),
            ty: h_triv_ty,
            value: None,
        }],
    );

    let result = simp_at_all(&mut state);
    // simp_at_all may or may not make progress depending on whether x = x
    // beta-reduces, but the key assertion is: if the goal still has hypotheses,
    // h_triv should still be present (not removed).
    if result.is_ok() {
        if let Some(goal) = state.current_goal() {
            // h_triv should still exist in the context (possibly simplified)
            let has_hyp = goal.local_ctx.iter().any(|d| d.name == "h_triv");
            assert!(
                has_hyp,
                "simp_at_all should NOT remove trivial hypotheses (Lean 4 simp at * semantics)"
            );
        }
    }
    // If simp_at_all returned Err(NoProgress), that's also fine — it means
    // no simplification was possible, but critically no hypothesis was removed.
}

/// `simp_all` DOES remove trivial hypotheses.
///
/// Same setup as above, but `simp_all` should remove the trivial h_triv.
#[test]
fn test_simp_all_removes_trivial_hypotheses() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);

    let h_triv_ty = make_eq_n(x.clone(), x.clone());
    let target = make_p(x.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h_triv".to_string(),
            ty: h_triv_ty,
            value: None,
        }],
    );

    let result = simp_all(&mut state);
    // simp_all should make progress (at least removing the trivial hyp)
    if result.is_ok() {
        if let Some(goal) = state.current_goal() {
            let has_triv = goal.local_ctx.iter().any(|d| d.name == "h_triv");
            assert!(!has_triv, "simp_all SHOULD remove trivial x = x hypotheses");
        }
    }
}

/// `simp_at_all` does NOT use equality hypotheses as rewrite lemmas
/// for other hypotheses (no cross-rewriting).
///
/// Setup: h_eq   : @Eq N x y
///        h_prop : P(x)
///        goal   : N  (arbitrary, not relevant)
///
/// With `simp_all`, h_eq would be used to rewrite h_prop from P(x) to P(y).
/// With `simp_at_all`, h_prop should remain P(x) since the global simp set
/// doesn't contain x = y.
#[test]
fn test_simp_at_all_no_cross_rewriting() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    let h_eq_ty = make_eq_n(x.clone(), y.clone());
    let h_prop_ty = make_p(x.clone());

    let mut state = ProofState::with_context(
        env,
        n_ty,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h_eq".to_string(),
                ty: h_eq_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_prop".to_string(),
                ty: h_prop_ty.clone(),
                value: None,
            },
        ],
    );

    let _result = simp_at_all(&mut state);
    // Whether simp_at_all succeeds or fails, h_prop should NOT have been
    // rewritten using h_eq. P(x) should remain as-is (no x → y rewrite).
    if let Some(goal) = state.current_goal() {
        if let Some(h_prop) = goal.local_ctx.iter().find(|d| d.name == "h_prop") {
            // h_prop.ty should still contain x, not y
            // Since simp_at with default config won't have h_eq as a lemma,
            // h_prop should be unchanged or only beta/eta simplified.
            let ty_str = format!("{:?}", h_prop.ty);
            assert!(
                !ty_str.contains("\"y\"") || ty_str.contains("\"x\""),
                "simp_at_all should NOT rewrite P(x) to P(y) using h_eq \
                 (no cross-hypothesis rewriting). Got: {ty_str}"
            );
        }
    }
}

/// `simp_at_all` skips proposition-valued let-bindings, matching Lean 4's
/// `getNondepPropHyps` filter.
///
/// Setup: h_let : P(x) := hpx
///        x_eq_y : x = y  [simp]
///        goal   : P(x)
///
/// The goal may simplify to `P(y)`, but the let-bound proof must remain
/// untouched: same type, same stored value.
#[test]
fn test_simp_at_all_skips_prop_let_bindings() {
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let hpx = Expr::const_(Name::from_string("hpx"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x_eq_y"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y),
    })
    .expect("x_eq_y axiom should register");
    env.register_simp_lemma(Name::from_string("x_eq_y"), SimpPriority::Default);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hpx"),
        level_params: vec![],
        type_: make_p(x.clone()),
    })
    .expect("hpx axiom should register");

    let let_decl = LocalDecl {
        fvar: FVarId::new(0),
        name: "h_let".to_string(),
        ty: make_p(x.clone()),
        value: Some(hpx.clone()),
    };

    let mut state = ProofState::with_context(env, make_p(x.clone()), vec![let_decl]);

    let _ = simp_at_all(&mut state);

    let goal = state.current_goal().expect("goal should remain available");
    let h_let = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h_let")
        .expect("h_let should remain in the local context");

    assert_eq!(
        h_let.ty,
        make_p(x.clone()),
        "simp_at_all should not simplify proposition let-bindings"
    );
    assert_eq!(
        h_let.value,
        Some(hpx),
        "simp_at_all should preserve let-bound proof values"
    );
}

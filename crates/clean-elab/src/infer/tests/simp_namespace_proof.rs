// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression: `simp [extra-lemma]` resolves unqualified extra-lemma
//! names through opened namespaces.
//!
//! After `open Nat`, `simp [add_zero]` must reach `Nat.add_zero` rather than
//! looking the literal `add_zero` up in the environment and missing. The fix
//! threads the elaborator's `NamespaceState` into the `ProofState` so the simp
//! lemma path can use the same `resolve_identifier` order as term references.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::{Environment, Expr, Level, Name};
use clean_parser::{parse_expr, SurfaceExpr};

/// Build an environment with `Nat`, `Eq`, two constants `a b : Nat`, and a
/// qualified rewrite lemma `Nat.add_zero : @Eq Nat b a` (rewrites `b → a`).
///
/// Target: `@Eq Nat b a`. `simp only [add_zero]` (with `open Nat`) rewrites the
/// LHS `b → a`, leaving `a = a`, closed by `rfl`.
fn setup_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_nat().expect("init nat");
    env.init_eq().expect("init eq");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_u1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("register const");
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Nat.add_zero : @Eq Nat b a  (rewrites b → a)
    let eq_ba = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), b.clone()),
        a.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.add_zero"),
        level_params: vec![],
        type_: eq_ba,
    })
    .expect("register Nat.add_zero");

    // Target: @Eq Nat b a
    let target = Expr::app(Expr::app(Expr::app(eq_u1, nat), b), a);
    (env, target)
}

fn by_tactics(src: &str) -> Vec<clean_parser::SurfaceTactic> {
    let surface = parse_expr(src).expect("by-tactic expression should parse");
    match surface {
        SurfaceExpr::ByTactic(_, tactics) => tactics,
        other => panic!("expected a ByTactic surface expression, got {other:?}"),
    }
}

/// The gap: with `open Nat` threaded into the proof state, `simp only [add_zero]`
/// resolves the unqualified `add_zero` to `Nat.add_zero` and closes the goal.
#[test]
fn test_simp_only_opened_namespace_resolves_extra_lemma() {
    let (env, target) = setup_env();
    let tactics = by_tactics("by simp only [add_zero]");

    let mut ctx = ElabCtx::new(&env);
    // open Nat
    let mut ns = crate::namespace::NamespaceState::new();
    ns.open_namespace(Name::from_string("Nat"));
    ctx.set_namespace_state(ns);
    ctx.current_expected_type = Some(target.clone());

    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("simp only [add_zero] under `open Nat` should close `b = a`");

    assert!(
        !proof.has_fvar_quick(),
        "proof should be closed, got: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elaborated proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "proof type should match the original target"
    );
}

/// Regression: a bare qualified name still works with the namespace threaded.
#[test]
fn test_simp_only_qualified_extra_lemma_still_closes() {
    let (env, target) = setup_env();
    let tactics = by_tactics("by simp only [Nat.add_zero]");

    let mut ctx = ElabCtx::new(&env);
    let mut ns = crate::namespace::NamespaceState::new();
    ns.open_namespace(Name::from_string("Nat"));
    ctx.set_namespace_state(ns);
    ctx.current_expected_type = Some(target.clone());

    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("simp only [Nat.add_zero] should close `b = a`");
    assert!(!proof.has_fvar_quick());
}

/// Without an `open`, the unqualified extra-lemma name does not resolve, so the
/// rewrite never fires and the goal `b = a` stays open — surfacing as an error
/// rather than a silent or unsound close.
#[test]
fn test_simp_only_unqualified_without_open_leaves_goal_open() {
    let (env, target) = setup_env();
    let tactics = by_tactics("by simp only [add_zero]");

    let mut ctx = ElabCtx::new(&env);
    // No `open Nat` — namespace state is empty.
    ctx.current_expected_type = Some(target);

    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "without `open Nat`, `simp only [add_zero]` must not close `b = a`"
    );
}

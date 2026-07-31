// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `whnf` is NOT a function of `(env, expr)` alone — its RESULT depends on the
//! heartbeat budget. Pinned here because it bounds what a Phase-2 correspondence
//! proof can state.
//!
//! On exhaustion `whnf` returns the term UNREDUCED (`tc/whnf.rs:188-190`). That
//! is deliberate and SOUND — a less-reduced term is still definitionally equal,
//! so the checker can never accept a non-equality this way; the error surfaces at
//! the next `tick_heartbeat()` in `infer_type`. But it does mean the function is
//! budget-dependent, so a total-function statement `whnf : Env -> Expr -> Expr`
//! is not faithful to the implementation: the budget is a third input.
//!
//! See `docs/plans/PHASE2_CHECKER_SPINE_SCOPE_2026-07-25.md` blocker 3.

use clean_kernel::{BinderInfo, Environment, Expr, Level, TypeChecker};

/// `fun (x : Prop) => x`
fn id_fn() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    )
}

/// `id (id (... (id base)))` — n weak-head beta steps to reach `base`.
fn beta_chain(n: usize, base: Expr) -> Expr {
    let mut e = base;
    for _ in 0..n {
        e = Expr::app(id_fn(), e);
    }
    e
}

fn whnf_at_budget(limit: u32, e: &Expr) -> Expr {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(limit);
    tc.reset_heartbeat();
    tc.whnf(e)
}

#[test]
fn whnf_returns_input_unreduced_when_budget_is_exhausted() {
    let base = Expr::sort(Level::succ(Level::zero()));
    let term = beta_chain(40, base.clone());

    // Budget 1: the counter is spent by the entry tick, so whnf bails BEFORE any
    // reduction and hands back its input verbatim.
    let starved = whnf_at_budget(1, &term);
    assert_eq!(
        starved, term,
        "with an exhausted budget whnf must return its input unreduced (the sound bail)"
    );
    assert_ne!(
        starved, base,
        "if this reduced anyway, the heartbeat bail is not being taken and this test is vacuous"
    );
}

#[test]
fn whnf_reduces_fully_when_budget_suffices() {
    let base = Expr::sort(Level::succ(Level::zero()));
    let term = beta_chain(40, base.clone());
    assert_eq!(
        whnf_at_budget(10_000, &term),
        base,
        "with budget the same term must reach its weak-head normal form"
    );
}

/// THE POINT: same environment, same expression, two different results. So
/// `whnf` is not a function of `(env, expr)`, and any correspondence statement
/// must carry the budget (or prove the budget never binds).
#[test]
fn same_env_and_expr_yield_different_results_across_budgets() {
    let base = Expr::sort(Level::succ(Level::zero()));
    let term = beta_chain(40, base.clone());
    let starved = whnf_at_budget(1, &term);
    let funded = whnf_at_budget(10_000, &term);
    assert_ne!(
        starved, funded,
        "whnf must be budget-dependent for the Phase-2 caveat to be real; if these ever \
         agree, re-derive the caveat instead of deleting this test"
    );
    // ...and the difference is in the SOUND direction: the starved run is
    // less-reduced, never a different normal form.
    assert_eq!(
        starved, term,
        "the starved result must be the unreduced input"
    );
    assert_eq!(funded, base, "the funded result must be the normal form");
}

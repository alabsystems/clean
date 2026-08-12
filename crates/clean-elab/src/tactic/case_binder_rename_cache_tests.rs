// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression test for `case`/`next` binder renaming and TypeChecker-cache
//! invalidation (RC-P).
//!
//! `rename_case_binders` mutated the focused goal through
//! `ps.goals.front_mut()`, which bypasses `current_goal_mut()`'s
//! `invalidate_tc_cache()`. The cache is keyed by the goal's `meta_id` — which a
//! rename does not change — so the stale `TcCaches` stayed live across the
//! context mutation and a later `with_tc` call could answer from the pre-rename
//! state. Every other context-mutating tactic invalidates; this one only did so
//! by accident, when some earlier step happened to clear the cache first.

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

use super::builtins_compound::rename_case_binders;
use super::core::ProofState;
use super::proof_manipulation::cases;
use super::proof_term::intro;

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

#[test]
fn test_rename_case_binders_invalidates_type_checker_cache() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let mut state = ProofState::new(env, Expr::arrow(nat_ty(), nat_ty()));
    intro(&mut state, "n").expect("intro n");
    cases(&mut state, "n").expect("cases n");

    // Focus the `succ` branch the way the `case`/`next` handler does, so the
    // goal carries an auto-generated field (`succ_0`) to rename.
    let succ_pos = state
        .goals()
        .iter()
        .position(|g| g.tag.as_deref() == Some("succ"))
        .expect("cases should tag a `succ` branch");
    state.goals.swap(0, succ_pos);

    // Warm the TypeChecker cache against THIS goal (the cache is keyed by
    // `meta_id`, so it stays applicable across a rename).
    let goal = state.current_goal().expect("focused goal").clone();
    let _ = state.is_def_eq(&goal, &nat_ty(), &nat_ty());
    assert!(
        state.has_tc_cache_for_test(),
        "a def-eq check on the focused goal should populate the TypeChecker cache"
    );

    rename_case_binders(&mut state, &["m".to_string()]);

    assert!(
        !state.has_tc_cache_for_test(),
        "renaming the focused case's binders mutates its local context, so it MUST \
         invalidate the TypeChecker cache (route through `current_goal_mut`)"
    );
    let ctx = &state.goals()[0].local_ctx;
    assert!(
        ctx.iter().any(|d| d.name == "m"),
        "the `succ` field should have been renamed to `m`, got {ctx:?}"
    );
}

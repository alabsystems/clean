// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness tests for batch verifier cache sharing.
//!
//! Tests FVarId collision in cross-expression WHNF cache sharing.
//! Part of #2382 do-audit.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Regression test: FVarId collision in cross-expression WHNF cache sharing.
///
/// Before the fix (#2382), the batch verifier shared WHNF caches across
/// expressions but each expression got a fresh LocalContext (next_id=0).
/// This broke the FVarId-unreachability invariant: FVar(0) from TC1 and
/// FVar(0) from TC2 had different meanings but the cache treated them
/// as the same key, returning stale values.
///
/// The fix: `TcCaches` now carries `next_fvar_id` from `take_caches()`.
/// `with_mode_and_caches()` advances the new LocalContext's counter to
/// at least `next_fvar_id`, preventing ID reuse.
///
/// Verifies at the WHNF level:
/// 1. TC1: push let-FVar(0) with value Sort(0), WHNF(FVar(0)) → Sort(0), cached
/// 2. Extract caches (next_fvar_id=1), create TC2 with caches
/// 3. TC2: push let-binding → gets FVar(1) (no collision with FVar(0))
/// 4. WHNF(FVar(1)) returns correct value (Nat), not stale cache
///
/// Part of #2382 — FVarId-unreachability invariant for batch cache sharing
#[test]
fn test_cache_sharing_fvarid_collision_soundness() {
    let env = Environment::with_prelude();

    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::Zero))); // Sort(1) = Type
    let prop = Expr::from_kind(ExprKind::Sort(Level::Zero)); // Sort(0) = Prop
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // TC1: fresh context, push FVar(0) as let-binding to Sort(0)
    let tc1 = TypeChecker::new(&env);
    let fvar_id1 = tc1.ctx_push_let(Name::anon(), type_.clone(), prop.clone());
    assert_eq!(fvar_id1, FVarId(0), "First FVar should be FVar(0)");

    // WHNF(FVar(0)) with let-value Sort(0) → Sort(0)
    let fvar_expr = Expr::fvar(FVarId(0));
    let whnf_result1 = tc1.whnf(&fvar_expr);
    assert_eq!(
        whnf_result1, prop,
        "TC1: WHNF(FVar(0)) should be Sort(0) (let-value)"
    );

    // Extract caches (including whnf[FVar(0)] = Sort(0), next_fvar_id=1)
    let caches = tc1.take_caches();
    tc1.ctx_pop();

    // TC2: with caches from TC1 — next_fvar_id prevents ID collision
    let tc2 = TypeChecker::with_mode_and_caches(&env, crate::CleanMode::default(), caches);
    let fvar_id2 = tc2.ctx_push_let(Name::anon(), type_, nat.clone());

    // FIX VERIFIED: TC2 allocates FVar(1), not FVar(0)
    assert_ne!(
        fvar_id2,
        FVarId(0),
        "next_fvar_id propagation must prevent FVarId collision"
    );
    assert_eq!(
        fvar_id2,
        FVarId(1),
        "TC2 should allocate FVar(1) (after TC1's FVar(0))"
    );

    // WHNF of TC2's FVar returns the correct let-value (Nat)
    let fvar_expr2 = Expr::fvar(fvar_id2);
    let whnf_result2 = tc2.whnf(&fvar_expr2);
    assert_eq!(
        whnf_result2, nat,
        "TC2: WHNF(FVar(1)) should be Nat (the current let-value)"
    );
    tc2.ctx_pop();
}

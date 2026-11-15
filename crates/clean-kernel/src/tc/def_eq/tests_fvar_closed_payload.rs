// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Context membership depends on free-variable-bearing paths, not closed
//! program/JSON payload size. These are structural guards, not typing rules.

use super::*;
use crate::env::Environment;
use crate::expr::BinderInfo;
use std::sync::Arc;

#[test]
fn test_fvar_context_closed_payload_cost_preserves_live_and_stale_membership() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let live = tc.push_binder_local(
        Name::from_string("live"),
        Expr::type_(),
        BinderInfo::Default,
    );
    let atom = Arc::new(Expr::type_());
    let mut payload = atom.clone();
    for _ in 0..50_000 {
        payload = Arc::new(Expr::app_arc(payload, atom.clone()));
    }
    assert!(!payload.has_fvar_quick());
    let retained = Arc::downgrade(&payload);
    let open = Arc::new(Expr::fvar(live));
    let forward = Expr::app_arc(open.clone(), payload.clone());
    let reverse = Expr::app_arc(payload.clone(), open);

    let check = |expected| {
        for root in [&forward, &reverse] {
            // Per-thread work counts, not a timing threshold or a larger budget.
            let _ = crate::work_meter::stats::take();
            assert_eq!(tc.all_fvars_in_context(root), expected);
            let work = crate::work_meter::stats::take();
            assert_eq!(
                work.equiv_nodes, 2,
                "only the open root and FVar need membership checks"
            );
        }
    };
    check(true);
    check(true); // Warm walks still perform the same exact membership checks.
    tc.pop_binder_local();
    check(false);
    let sibling = tc.push_binder_local(
        Name::from_string("sibling"),
        Expr::type_(),
        BinderInfo::Default,
    );
    assert_ne!(sibling, live);
    check(false); // Same context length cannot revive the popped variable.
    tc.pop_binder_local();
    let fresh = TypeChecker::new(&env);
    assert!(!fresh.all_fvars_in_context(&forward));
    assert!(!fresh.all_fvars_in_context(&reverse));

    drop(forward);
    drop(reverse);
    drop(payload);
    assert!(
        retained.upgrade().is_none(),
        "closed payload uses ordinary iterative destruction"
    );
}

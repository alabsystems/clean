// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! de Bruijn lift/instantiate round-trip + no-index-escape (design §8 tier 1).
//!
//! We build trusted `Term`s through the validation chokepoint (the only public
//! way to make one), then exercise lift/instantiate and assert closedness is
//! preserved (no loose variable escapes).

use clean_ck0::{MinimalEnv, RawExpr, RawLevel, Term};
use proptest::prelude::*;

/// Build a closed trusted Term from a RawExpr (panics on validation failure —
/// the strategy only produces closed terms).
fn validate_closed(raw: &RawExpr) -> Term {
    let env = MinimalEnv::new();
    Term::validate_closed(&env, raw).expect("strategy produces closed terms")
}

#[test]
fn test_identity_lambda_is_closed() {
    // λ x. x  == Lam(_, Sort 0, BVar 0)
    let raw = RawExpr::Lam(
        Default::default(),
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    );
    let t = validate_closed(&raw);
    assert!(!t.has_loose_bvars(), "λx.x is closed");
}

#[test]
fn test_validate_rejects_open_var() {
    // BVar(0) with no enclosing binder is open and must be rejected.
    let env = MinimalEnv::new();
    let raw = RawExpr::BVar(0);
    let r = Term::validate_closed(&env, &raw);
    assert!(r.is_err(), "open BVar must be rejected by the chokepoint");
}

#[test]
fn test_lift_zero_is_identity() {
    let raw = RawExpr::Lam(
        Default::default(),
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    );
    let t = validate_closed(&raw);
    assert_eq!(t.lift(0), t);
}

#[test]
fn test_lift_of_closed_is_identity() {
    // Closed terms are unaffected by lift for any amount.
    let raw = RawExpr::Lam(
        Default::default(),
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    );
    let t = validate_closed(&raw);
    assert_eq!(t.lift(5), t);
    assert_eq!(t.lift(1000), t);
}

#[test]
fn test_beta_instantiate_identity_application() {
    // (λx.x) applied: instantiate body BVar(0) with a closed value v yields v.
    let body = validate_inner_bvar0();
    // value: λy.y  (closed)
    let v = validate_closed(&RawExpr::Lam(
        Default::default(),
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    ));
    let result = body.instantiate(&v);
    assert_eq!(result, v, "BVar(0)[v] == v");
    assert!(!result.has_loose_bvars());
}

/// Build the body `BVar(0)` validated in a context of depth 1 (i.e. under one
/// binder), so it is a *trusted* term with a loose var bound by that binder.
fn validate_inner_bvar0() -> Term {
    let env = MinimalEnv::new();
    Term::validate(&env, &RawExpr::BVar(0), 1, 0).expect("BVar(0) closed under depth-1 context")
}

// --- property tests: closedness preserved, no index escape ---

/// A strategy producing closed RawExprs (de Bruijn correct by construction).
/// `depth` is the number of enclosing binders available for BVars, `fuel`
/// bounds the tree height (manual recursion bound — `prop_recursive` cannot
/// thread the changing `depth` through binders).
fn arb_closed_raw(depth: u32, fuel: u32) -> BoxedStrategy<RawExpr> {
    let leaf: BoxedStrategy<RawExpr> = if depth == 0 {
        Just(RawExpr::Sort(RawLevel::Zero)).boxed()
    } else {
        prop_oneof![
            Just(RawExpr::Sort(RawLevel::Zero)),
            (0..depth).prop_map(RawExpr::BVar),
        ]
        .boxed()
    };
    if fuel == 0 {
        return leaf;
    }
    let d = depth;
    let f = fuel.saturating_sub(1);
    prop_oneof![
        2 => leaf,
        1 => (arb_closed_raw(d, f), arb_closed_raw(d, f))
            .prop_map(|(g, a)| RawExpr::App(Box::new(g), Box::new(a))),
        1 => (arb_closed_raw(d, f), arb_closed_raw(d.saturating_add(1), f)).prop_map(|(ty, body)| {
            RawExpr::Lam(Default::default(), Box::new(ty), Box::new(body))
        }),
        1 => (arb_closed_raw(d, f), arb_closed_raw(d.saturating_add(1), f)).prop_map(|(ty, body)| {
            RawExpr::Pi(Default::default(), Box::new(ty), Box::new(body))
        }),
    ]
    .boxed()
}

proptest! {
    #[test]
    fn prop_closed_terms_validate_and_stay_closed(raw in arb_closed_raw(0, 4)) {
        let env = MinimalEnv::new();
        let t = Term::validate_closed(&env, &raw)
            .expect("closed raw validates");
        prop_assert!(!t.has_loose_bvars(), "validated closed term has no loose bvars");
    }

    #[test]
    fn prop_lift_then_closed_preserved(raw in arb_closed_raw(0, 4), amount in 0u32..1000) {
        let env = MinimalEnv::new();
        let t = Term::validate_closed(&env, &raw).expect("validates");
        let lifted = t.lift(amount);
        // Lifting a closed term changes nothing (no loose var to shift).
        prop_assert_eq!(&lifted, &t);
        prop_assert!(!lifted.has_loose_bvars());
    }

    #[test]
    fn prop_instantiate_under_one_binder_no_escape(raw in arb_closed_raw(1, 4)) {
        // `raw` is closed under one binder => a trusted term with at most BVar(0)
        // loose. Instantiating with a closed value must yield a closed term: no
        // index escapes.
        let env = MinimalEnv::new();
        let body = Term::validate(&env, &raw, 1, 0).expect("validates under depth 1");
        let v = Term::validate_closed(&env, &RawExpr::Sort(RawLevel::Zero)).expect("v");
        let r = body.instantiate(&v);
        prop_assert!(!r.has_loose_bvars(), "instantiate closes the one loose binder; no escape");
    }

    #[test]
    fn prop_cached_hash_correct(raw in arb_closed_raw(0, 4)) {
        let env = MinimalEnv::new();
        let t = Term::validate_closed(&env, &raw).expect("validates");
        prop_assert_eq!(t.cached_hash(), t.recompute_hash());
    }
}

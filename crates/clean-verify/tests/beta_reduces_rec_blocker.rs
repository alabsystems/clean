// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression for the (now retired) `beta_reduces.rec` -> `DefEq` blocker.
//!
//! HISTORY. This file used to pin a BLOCKER: the direct `beta_reduces.rec` route
//! could not discharge the `beta` / `let_` arms because `DefEq.beta` carried
//! typing premises that `beta_reduces` does not provide, and the typed alias
//! `beta_reduction` is now 8-ary (A b a B u + three `Typing` premises) — feeding
//! it the three `beta_reduces.rec` arguments UNDER-APPLIES the typed beta and the
//! elaborator chokes on the residual `forall`. That demonstration term is DEAD:
//! `DefEq.beta` is now UNTYPED (church_rosser_whnf retirement), so the bridge is a
//! genuine kernel-checked `beta_reduces.rec` term over the untyped `DefEq`
//! constructors. These tests now lock in the PROVED state.

use clean_verify::test_utils::build_spec_with_stack;
use clean_verify::ProofStatus;
use clean_verify::Specification;

fn build_spec() -> Specification {
    build_spec_with_stack()
}

/// The former blocker is retired: the bridge is a real kernel-checked
/// `beta_reduces.rec` term, so re-verifying it in the spec env succeeds.
#[test]
fn beta_reduces_rec_bridge_now_constructively_checks() {
    let spec = build_spec();

    // Kernel re-check of the registered proof term: the untyped `beta_reduces.rec`
    // bridge type-checks against `beta_reduces e e' -> DefEq e e'` in the spec env.
    spec.verify_definition("beta_reduces_preserves_def_eq").expect(
        "beta_reduces_preserves_def_eq should kernel-typecheck via the untyped beta_reduces.rec bridge",
    );

    let def = spec
        .definitions()
        .get("beta_reduces_preserves_def_eq")
        .expect("beta_reduces_preserves_def_eq should exist");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_preserves_def_eq is now constructively proved via untyped beta_reduces.rec"
    );
    assert!(
        def.value_src.is_some(),
        "beta_reduces_preserves_def_eq should carry the beta_reduces.rec proof term"
    );
}

#[test]
fn beta_reduces_wrapper_bridge_is_proved() {
    let spec = build_spec();
    let def = spec
        .definitions()
        .get("beta_reduces_preserves_def_eq")
        .expect("beta_reduces_preserves_def_eq should exist");

    assert!(
        !def.is_axiom,
        "beta_reduces_preserves_def_eq should not be an axiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_preserves_def_eq is constructively proved (untyped DefEq.beta unblocks it)"
    );
    assert!(
        def.value_src.is_some(),
        "beta_reduces_preserves_def_eq should carry a proof term"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("beta_reduces_preserves_def_eq should record dependencies");
    for expected in [
        "beta_reduces.rec",
        "beta_reduces_def_eq_goal",
        "DefEq.beta",
        "DefEq.app_cong",
        "DefEq.lam_cong",
        "DefEq.pi_cong",
        "DefEq.iota",
        "DefEq.refl",
        "DefEq.trans",
    ] {
        assert!(
            deps.contains(expected),
            "beta_reduces_preserves_def_eq should route through {expected}: {deps:?}"
        );
    }
}

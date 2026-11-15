// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins (R176): the oracle's reading of a container's parameter, kept as it
//! was. Each compares the one pass with the rules on a container whose
//! parameter type binds a variable.

use super::{app, check, check_before, konst, lam, n, pi, ty, with_container};
use crate::minimal_env::MinimalEnv;
use crate::term::Term;

/// `Q (α : F (λ (x : Type). x))`: at depth 0 nothing reads parameter 0, so
/// the `x` the λ binds is not it and `F`, no inductive, is never asked about.
/// A pass without the depth mask (`Target::read_at`) refuses `Q T → T`.
#[test]
fn test_positivity_binder_in_a_parameter_type_at_its_own_depth_is_not_the_parameter() {
    let dom = app(konst("F"), lam(ty(), Term::bvar(0)));
    let env = with_container(
        MinimalEnv::new(),
        "Q",
        1,
        vec![pi(dom, app(konst("Q"), Term::bvar(0)))],
    );
    let ctor = pi(app(konst("Q"), konst("T")), konst("T"));
    assert_eq!(check_before(&env, &[n("T")], &ctor), Ok(()));
    assert_eq!(check(&env, &[n("T")], &ctor), Ok(()));
}

/// The other side of that reading, an over-refusal kept as the oracle made
/// it: in `Q (α : (x : Type) → (x → Nat) → Nat)` the `x` under the second
/// binder is read as parameter 0, left of an arrow, so slot 0 is not strictly
/// positive although nothing uses `α`. Fails loudly the day the reading is
/// fixed (a fidelity change for its own decision record).
#[test]
fn test_positivity_binder_in_a_parameter_type_past_its_depth_is_read_as_the_parameter() {
    let dom = pi(ty(), pi(pi(Term::bvar(0), konst("Nat")), konst("Nat")));
    let env = with_container(
        MinimalEnv::new(),
        "Q",
        1,
        vec![pi(dom, app(konst("Q"), Term::bvar(0)))],
    );
    let ctor = pi(app(konst("Q"), konst("T")), konst("T"));
    assert_eq!(check_before(&env, &[n("T")], &ctor), Err(()));
    assert_eq!(check(&env, &[n("T")], &ctor), Err(()));
}

/// The same reading through an argument: `Q (α : F (λ (x : Type). (x → Nat)
/// → Nat))`. The argument mentions no parameter at depth 0, yet the oracle
/// walked it and refused at the arrow under the λ, so the cheap fix (skip an
/// argument that mentions nothing) is not verdict-preserving in a container's
/// scan, only in a block's.
#[test]
fn test_positivity_binder_under_a_lambda_in_a_parameter_type_is_read_as_the_parameter() {
    let body = pi(pi(Term::bvar(0), konst("Nat")), konst("Nat"));
    let dom = app(konst("F"), lam(ty(), body));
    let env = with_container(
        MinimalEnv::new(),
        "Q",
        1,
        vec![pi(dom, app(konst("Q"), Term::bvar(0)))],
    );
    let ctor = pi(app(konst("Q"), konst("T")), konst("T"));
    assert_eq!(check_before(&env, &[n("T")], &ctor), Err(()));
    assert_eq!(check(&env, &[n("T")], &ctor), Err(()));
}

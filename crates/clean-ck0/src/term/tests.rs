// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::minimal_env::MinimalEnv;
use crate::validate::Env;

#[test]
fn test_structural_equality_with_matching_hash() {
    // Two independently built identical terms are == (and share a hash).
    let a = Term::app(Term::bvar(0), Term::sort(Level::zero()));
    let b = Term::app(Term::bvar(0), Term::sort(Level::zero()));
    assert_eq!(a, b);
    assert_eq!(a.cached_hash(), b.cached_hash());
}

#[test]
fn test_different_terms_differ() {
    let a = Term::bvar(0);
    let b = Term::bvar(1);
    assert_ne!(a, b);
}

#[test]
fn test_cached_hash_equals_recompute() {
    let t = Term::lam(
        BinderInfo::Default,
        Term::sort(Level::zero()),
        Term::app(Term::bvar(0), Term::bvar(0)),
    );
    assert_eq!(t.cached_hash(), t.recompute_hash());
}

#[test]
fn test_has_loose_tracks_binders() {
    // lambda over BVar(0) is closed; BVar(0) alone is loose.
    let closed = Term::lam(
        BinderInfo::Default,
        Term::sort(Level::zero()),
        Term::bvar(0),
    );
    assert!(!closed.has_loose_bvars());
    let loose = Term::bvar(0);
    assert!(loose.has_loose_bvars());
}

#[test]
fn test_constref_levels_match_env_arity() {
    let env: MinimalEnv = MinimalEnv::new().with_const(Name::from_dotted("Id"), 1);
    assert_eq!(env.num_level_params(&Name::from_dotted("Id")), Some(1));
    let c = ConstRef::mk(&env, Name::from_dotted("Id"), vec![Level::param(0)]).expect("ok");
    assert_eq!(c.levels().len(), 1);
}

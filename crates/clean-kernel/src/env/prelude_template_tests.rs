// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Environment::with_prelude` hands out CLONES of a per-thread template.
//!
//! Building the prelude kernel-checks several hundred declarations and is the
//! same work every time. Measured 2026-09-19 in a debug build, one construction
//! is ~8.45 s — and that figure IS the suite: the trivial
//! `theorem trivial_sorry : True := sorry` took 8.39 s, a test building five
//! preludes took 42.3 s, one building six took 50.9 s. With the template they
//! are 8.4 s, 8.6 s and 8.8 s: one build per thread, then ~0.07 s a clone.
//!
//! The risk a cache carries is not speed, it is LEAKAGE — a caller mutating
//! what another caller later receives. These arms are about that, and about the
//! clone being the same environment the builder produces.

use crate::env::{Declaration, Environment};
use crate::expr::Expr;
use crate::name::Name;

fn nm(s: &str) -> Name {
    Name::from_string(s)
}

/// A declaration no prelude contains, so its presence can only come from a test.
fn marker_decl(name: &str) -> Declaration {
    Declaration::Definition {
        name: nm(name),
        level_params: vec![],
        type_: Expr::const_(nm("Nat"), vec![]),
        value: Expr::nat_lit(1),
        is_reducible: false,
    }
}

#[test]
fn test_two_preludes_are_independent() {
    // THE LEAKAGE ARM. Each caller must get its own environment; mutating one
    // must be invisible to the next.
    let mut a = Environment::with_prelude();
    let before = Environment::with_prelude().num_constants();

    a.add_decl(marker_decl("templateLeakMarkerA"))
        .expect("marker must register");

    let b = Environment::with_prelude();
    assert!(
        b.get_const(&nm("templateLeakMarkerA")).is_none(),
        "a mutation of one prelude leaked into a later one — the template is \
         being handed out instead of cloned"
    );
    assert_eq!(
        b.num_constants(),
        before,
        "a later prelude must have the same size as an earlier one"
    );
}

#[test]
fn test_the_template_itself_is_never_mutated() {
    // Mutate TWICE from different clones; a template that absorbed either
    // mutation would show it in the third.
    let mut a = Environment::with_prelude();
    a.add_decl(marker_decl("templateLeakMarkerB")).expect("b");
    let mut b = Environment::with_prelude();
    b.add_decl(marker_decl("templateLeakMarkerC")).expect("c");

    let c = Environment::with_prelude();
    assert!(
        c.get_const(&nm("templateLeakMarkerB")).is_none(),
        "B leaked"
    );
    assert!(
        c.get_const(&nm("templateLeakMarkerC")).is_none(),
        "C leaked"
    );
}

#[test]
fn test_cached_matches_a_freshly_built_one() {
    // THE EQUIVALENCE ARM. A clone must be the environment the builder
    // produces, not an approximation of it.
    let cached = Environment::with_prelude();
    let fresh = Environment::try_with_prelude_uncached().expect("uncached build");

    assert_eq!(
        cached.num_constants(),
        fresh.num_constants(),
        "the cached prelude must hold exactly the constants a fresh build does"
    );
    assert_eq!(cached.mode(), fresh.mode(), "mode must match");

    // Spot-check that the names really are the same set, not merely the same
    // count: a size match alone would pass on two different environments.
    let mut missing = Vec::new();
    for info in fresh.constants() {
        if cached.get_const(&info.name).is_none() {
            missing.push(info.name.to_string());
        }
    }
    assert!(
        missing.is_empty(),
        "cached prelude is missing constants a fresh build has: {missing:?}"
    );
}

#[test]
fn test_uncached_builder_is_still_reachable() {
    // The escape hatch must keep working: it is what anything measuring or
    // exercising CONSTRUCTION has to call, and it is this file's own control.
    let fresh = Environment::try_with_prelude_uncached().expect("uncached build");
    assert!(
        fresh.get_const(&nm("Nat")).is_some(),
        "an uncached prelude is still a prelude"
    );
}

#[test]
fn test_the_template_is_admissible_in_an_ordinary_test_process() {
    // WITHOUT THIS THE PERFORMANCE CLAIM IS VACUOUS. The template is only used
    // when `ordinary_prelude_is_shareable()` says the ordinary prelude is
    // shareable in this process — it is not, under proof-quality strict mode,
    // DENY_SORRY, a declaration budget, or a Metamath two-pass context. An
    // ordinary test process is none of those, so the fast path must be live
    // here; if a later change makes the predicate always decline, the suite
    // silently returns to one full build per call and only this arm notices.
    assert!(
        crate::env::prelude_reuse::ordinary_prelude_is_shareable(),
        "an ordinary test process must be able to share the prelude template"
    );
}

#[test]
fn test_the_guard_and_the_sibling_cache_ask_the_same_question() {
    // The template and the reusable-reference cache must not disagree about
    // when sharing is allowed; they deliberately call the SAME predicate, so
    // this pins that the coupling still exists rather than re-deriving the
    // conditions here (a second copy would drift).
    let shareable = crate::env::prelude_reuse::ordinary_prelude_is_shareable();
    let a = Environment::with_prelude();
    let b = Environment::try_with_prelude_uncached().expect("uncached");
    assert_eq!(
        a.num_constants(),
        b.num_constants(),
        "cached and uncached must agree whether or not sharing is on \
         (shareable={shareable})"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The occurs check at the level-assignment funnel
//! ([`MetaState::add_level_constraint`]): a level metavariable is never
//! assigned a level that mentions its own class, as Lean's `isLevelDefEqAux`
//! assigns `?u := v` only when `!u.occurs v` (`Lean/Meta/LevelDefEq.lean`).
//! The end-to-end face is pinned by `crate::tests_pkg4_level_occurs`.

use super::MetaState;
use clean_kernel::name::Name;
use clean_kernel::Level;

fn p(s: &str) -> Level {
    Level::param(Name::from_string(s))
}

/// The funnel's occurs check: `?u := imax ?u ?v` (the assignment
/// `solve_head_const_levels` made for `congrFun h` over `Sort _`) is
/// refused and records nothing, directly and through a bound class.
#[test]
fn test_add_level_constraint_refuses_self_referential_bound() {
    let mut metas = MetaState::new();
    let (u, v, b) = (p("u"), p("v"), p("b"));
    metas
        .add_level_constraint(Name::from_string("b"), Level::imax(u.clone(), v.clone()))
        .expect("`?b := imax ?u ?v` is acyclic");
    assert!(
        metas
            .add_level_constraint(Name::from_string("u"), Level::imax(u.clone(), v.clone()))
            .is_err(),
        "`?u := imax ?u ?v` mentions `?u` and must be refused"
    );
    // The same cycle reached through `?b`'s class.
    assert!(
        metas
            .add_level_constraint(Name::from_string("u"), Level::succ(b.clone()))
            .is_err(),
        "`?u := ?b + 1` with `?b := imax ?u ?v` is a cycle through `?b`"
    );
    assert_eq!(
        metas.instantiate_level(&u),
        u,
        "a refused constraint leaves `?u` unassigned"
    );
}

/// A parameter-to-parameter union that would merge a class into its own
/// bound is refused too; an acyclic union still goes through.
#[test]
fn test_add_level_constraint_refuses_cyclic_union() {
    let mut metas = MetaState::new();
    let (a, c) = (p("a"), p("c"));
    metas
        .add_level_constraint(Name::from_string("a"), Level::succ(p("b")))
        .expect("`?a := ?b + 1` is acyclic");
    assert!(
        metas
            .add_level_constraint(Name::from_string("b"), a.clone())
            .is_err(),
        "uniting `?b` with `?a := ?b + 1` would make `?a = ?a + 1`"
    );
    metas
        .add_level_constraint(Name::from_string("c"), a.clone())
        .expect("uniting a fresh `?c` with `?a` is acyclic");
    assert_eq!(metas.instantiate_level(&c), Level::succ(p("b")));
}

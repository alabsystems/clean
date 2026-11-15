// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit gates for the two SPELLINGS of a `Nat` comparison.
//!
//! `a ≤ b` elaborates to `@LE.le Nat instLENat a b`; a hand-written Lean island
//! may instead write the kernel constant directly as `Nat.le a b`. The two are
//! definitionally equal (`instLENat` is a reducible wrapper), and
//! [`match_le_any`] / [`match_lt_any`] exist so that a tactic front end can see
//! both. The narrow [`match_le`] / [`match_lt`] keep their old typeclass-only
//! contract; these gates pin that split, because widening the narrow pair
//! instead would change every one of their other callers.
//!
//! The end-to-end consequence is locked separately in
//! `tests/omega_raw_nat_relation_spelling_e2e.rs`.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use crate::tactic::arith_push_neg::{
    is_raw_nat_rel, match_le, match_le_any, match_lt, match_lt_any, nat_le_raw, nat_lt_raw,
};
use crate::tactic::tc_app::{nat_le_tc, nat_lt_tc, nat_type};

fn v(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn is_nat_const(e: &Expr) -> bool {
    *e == nat_type()
}

// ---------------------------------------------------------------------------
// The typeclass spelling: unchanged, and matched by BOTH pairs
// ---------------------------------------------------------------------------

#[test]
fn typeclass_le_matches_narrow_and_any() {
    let e = nat_le_tc(v("a"), v("b"));
    let (ty, lhs, rhs) = match_le(&e).expect("narrow match_le must match the typeclass spine");
    assert!(is_nat_const(&ty));
    assert_eq!(lhs, v("a"));
    assert_eq!(rhs, v("b"));
    assert_eq!(match_le_any(&e), match_le(&e));
    assert!(!is_raw_nat_rel(&e));
}

#[test]
fn typeclass_lt_matches_narrow_and_any() {
    let e = nat_lt_tc(v("a"), v("b"));
    let (ty, lhs, rhs) = match_lt(&e).expect("narrow match_lt must match the typeclass spine");
    assert!(is_nat_const(&ty));
    assert_eq!(lhs, v("a"));
    assert_eq!(rhs, v("b"));
    assert_eq!(match_lt_any(&e), match_lt(&e));
    assert!(!is_raw_nat_rel(&e));
}

// ---------------------------------------------------------------------------
// The raw spelling: matched ONLY by the `_any` pair
// ---------------------------------------------------------------------------

#[test]
fn raw_le_matches_any_but_not_narrow() {
    let e = nat_le_raw(v("a"), v("b"));
    assert!(
        match_le(&e).is_none(),
        "narrow `match_le` must keep its typeclass-only contract"
    );
    let (ty, lhs, rhs) = match_le_any(&e).expect("match_le_any must match `Nat.le a b`");
    assert!(is_nat_const(&ty), "the raw spelling carries no type argument, so the type component must be the `Nat` constant");
    assert_eq!(lhs, v("a"));
    assert_eq!(rhs, v("b"));
    assert!(is_raw_nat_rel(&e));
}

#[test]
fn raw_lt_matches_any_but_not_narrow() {
    let e = nat_lt_raw(v("a"), v("b"));
    assert!(
        match_lt(&e).is_none(),
        "narrow `match_lt` must keep its typeclass-only contract"
    );
    let (ty, lhs, rhs) = match_lt_any(&e).expect("match_lt_any must match `Nat.lt a b`");
    assert!(is_nat_const(&ty));
    assert_eq!(lhs, v("a"));
    assert_eq!(rhs, v("b"));
    assert!(is_raw_nat_rel(&e));
}

// ---------------------------------------------------------------------------
// Scope: the two raw heads must not leak into each other, and nothing else
// may be admitted as a relation
// ---------------------------------------------------------------------------

#[test]
fn raw_heads_do_not_cross_match() {
    assert!(
        match_le_any(&nat_lt_raw(v("a"), v("b"))).is_none(),
        "`Nat.lt a b` is not a `≤`"
    );
    assert!(
        match_lt_any(&nat_le_raw(v("a"), v("b"))).is_none(),
        "`Nat.le a b` is not a `<`"
    );
}

/// `Nat.ble` / `Nat.blt` are the `Bool`-valued decisions, not relations. They
/// share the `Nat.` prefix and the arity, so an exact-name check is what keeps
/// them out.
#[test]
fn bool_valued_decisions_are_not_relations() {
    for head in ["Nat.ble", "Nat.blt", "Nat.beq", "Int.le", "Int.lt"] {
        let e = Expr::app(Expr::app(v(head), v("a")), v("b"));
        assert!(
            match_le_any(&e).is_none() && match_lt_any(&e).is_none(),
            "`{head}` must not be admitted as a Nat order relation"
        );
        assert!(!is_raw_nat_rel(&e));
    }
}

/// Arity is exact: a partially applied `Nat.le` is not a proposition, and an
/// over-applied one is not this shape either.
#[test]
fn raw_match_requires_exactly_two_arguments() {
    let partial = Expr::app(v("Nat.le"), v("a"));
    assert!(match_le_any(&partial).is_none());
    assert!(!is_raw_nat_rel(&partial));

    let over = Expr::app(Expr::app(Expr::app(v("Nat.le"), v("a")), v("b")), v("c"));
    assert!(match_le_any(&over).is_none());
    assert!(!is_raw_nat_rel(&over));

    let bare = v("Nat.le");
    assert!(match_le_any(&bare).is_none());
    assert!(!is_raw_nat_rel(&bare));
}

/// A `≤` at a carrier other than `Nat` still matches the TYPECLASS pair (it
/// always did) and reports its own carrier, so the `is_nat_type` guard in
/// `push_neg` keeps deciding what is rewritten — the `_any` widening adds the
/// raw `Nat` spelling and nothing else.
#[test]
fn typeclass_le_at_another_carrier_reports_that_carrier() {
    let e = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    v("Int"),
                ),
                v("instLEInt"),
            ),
            v("a"),
        ),
        v("b"),
    );
    let (ty, _, _) = match_le_any(&e).expect("the typeclass spine matches at any carrier");
    assert_eq!(ty, v("Int"));
    assert!(!is_raw_nat_rel(&e));
}

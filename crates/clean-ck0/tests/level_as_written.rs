// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ck0 refuses a level written in a form Lean's kernel reads differently from
//! ck0's canonical form (`docs/DECISIONS.md` R177, which R174's *Left as it
//! is* recorded). ck0 canonicalises each level as it is built: `imax a b` with
//! `b` never zero becomes `max a b`, renormalised, and an outer `succ` is
//! distributed into a `max`. Lean's `normalize` (`level.cpp`) rebuilds an
//! `imax` through `mk_imax` and stops, so it keeps `succ (max a b)` and an
//! unnormalised `max`, whether the `succ` is written or is the one the kernel
//! adds typing `Sort l` as `Sort (succ l)`; and Lean's kernel decides whether
//! a sort is `Prop`'s on its level as written. Validation refuses the three
//! forms that reach those differences (`src/validate/levels.rs`).
//!
//! Lean's verdicts here come from Lean's kernel: the declarations in
//! `fixtures/level_gap/`, handed to `addDeclCore`, and R150's 2,009 pairs of
//! levels with Lean's equality verdict (`clean-kernel/src/level/fixtures/`).
//! `level_as_written/lean.rs` ports Lean's level algebra for the random
//! pairs; its equality is checked against those 2,009 verdicts, and its
//! order, equality and `instantiate` against the 24 fixture rows each states
//! as one comparison. The random pairs compare ck0 with the port, not with
//! Lean's kernel.

#[path = "level_as_written/lean.rs"]
mod lean;

#[path = "level_as_written/residue.rs"]
mod residue;

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::term::TermKind;
use clean_ck0::{
    add_inductive, is_def_eq, Budget, Constructor, InductiveDecl, Level, MinimalEnv, Name, RawExpr,
    RawLevel, Term, Transparency, ValidateError, WrittenLevel,
};
use proptest::prelude::*;

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn u() -> Level {
    Level::param(0)
}

fn v() -> Level {
    Level::param(1)
}

fn raw_succ(l: RawLevel) -> RawLevel {
    RawLevel::Succ(Box::new(l))
}

fn raw_imax(a: RawLevel, b: RawLevel) -> RawLevel {
    RawLevel::IMax(Box::new(a), Box::new(b))
}

fn raw_max(a: RawLevel, b: RawLevel) -> RawLevel {
    RawLevel::Max(Box::new(a), Box::new(b))
}

fn sort(l: RawLevel, arity: u32) -> Result<Term, ValidateError> {
    Term::validate(&MinimalEnv::new(), &RawExpr::Sort(l), 0, arity)
}

fn refused_as(form: WrittenLevel) -> Result<Term, ValidateError> {
    Err(ValidateError::LevelAsWritten { form })
}

fn level_of(t: &Term) -> Level {
    match t.kind() {
        TermKind::Sort(l) => l.clone(),
        other => panic!("expected a sort, got {other:?}"),
    }
}

// --- ck0's level algebra, which validation now keeps such levels from ---

/// ck0's `succ (imax u (succ v))` is `max (succ u) (succ (succ v))`, where
/// Lean's `normalize` gives `succ (max u (succ v))`.
#[test]
fn test_level_succ_of_imax_with_succ_rhs_is_the_distributed_max() {
    let built = Level::succ(Level::imax(u(), Level::succ(v())));
    let distributed = Level::max(Level::succ(u()), Level::succ(Level::succ(v())));
    assert_eq!(built, distributed);
    // So ck0's order answers `true` where Lean's `is_geq_core`, comparing the
    // offsets of `succ (max u (succ v))` and `succ (succ v)`, answers `false`.
    assert!(Level::is_geq(&built, &Level::succ(Level::succ(v()))));
}

// --- the declarations of `fixtures/level_gap/`, now refused by name ---

/// `T.{u,v} : Sort (imax u (v+1) + 1)`. Lean's kernel refuses it with a field
/// `Sort (v+1)` and admits it with a field `Sort (imax u v)`
/// (`fixtures/level_gap/`); ck0 decided each the other way (R174). ck0 now
/// refuses the level, so it agrees with the first and refuses the second by
/// name, where before it refused it with a wrong reason.
#[test]
fn test_validate_imax_with_never_zero_rhs_under_succ_is_refused() {
    let top = raw_succ(raw_imax(RawLevel::Param(0), raw_succ(RawLevel::Param(1))));
    assert_eq!(sort(top, 2), refused_as(WrittenLevel::IMaxOfNeverZero));
}

/// The definition `Sort (imax u (v+1) + 2) := Sort (max u (v+1) + 1)`, which
/// Lean's kernel refuses and ck0 found equal.
#[test]
fn test_validate_definition_type_with_never_zero_imax_is_refused() {
    let ty = raw_succ(raw_succ(raw_imax(
        RawLevel::Param(0),
        raw_succ(RawLevel::Param(1)),
    )));
    assert_eq!(sort(ty, 2), refused_as(WrittenLevel::IMaxOfNeverZero));
}

/// `P.{u} : Sort (imax u 0)`, a `Prop` to ck0 and not to Lean's kernel,
/// which refuses it with a field `Type`.
#[test]
fn test_validate_imax_with_zero_rhs_is_refused() {
    let top = raw_imax(RawLevel::Param(0), RawLevel::Zero);
    assert_eq!(sort(top, 1), refused_as(WrittenLevel::ZeroOnceCanonical));
}

/// `Sort (max 0 0)` and `Sort (imax 0 0)`: Lean's kernel gives a type there no
/// proof irrelevance, and ck0 gave it a `Prop`'s.
#[test]
fn test_validate_max_and_imax_of_zeros_are_refused() {
    for l in [
        raw_max(RawLevel::Zero, RawLevel::Zero),
        raw_imax(RawLevel::Zero, RawLevel::Zero),
    ] {
        assert_eq!(sort(l, 0), refused_as(WrittenLevel::ZeroOnceCanonical));
    }
}

/// A zero form anywhere in the level, not only at its top: Lean's
/// `instantiate` keeps such a subterm as it is when a parameter around it
/// changes, so `max u (imax v 0)` at `u := 0` is `imax v 0` to Lean's kernel.
#[test]
fn test_validate_zero_form_inside_a_level_is_refused() {
    let l = raw_max(
        RawLevel::Param(0),
        raw_imax(RawLevel::Param(1), RawLevel::Zero),
    );
    assert_eq!(sort(l, 2), refused_as(WrittenLevel::ZeroOnceCanonical));
}

/// `imax a (max u v)` for each `a` by which the `imax` reduces to `max u v`
/// in both kernels: `0`, `1` (Lean's `mk_imax`), and `max u v` or `max v u`
/// (equal to the right side once normalised). Under a `succ`, written or the
/// one Lean's kernel adds typing `Sort l` as `Sort (succ l)`, Lean keeps
/// `succ (max u v)` and refuses it against `u` and against
/// `max (u+1) (v+1)` (the fixture's `C` rows); ck0's `max (u+1) (v+1)` would
/// admit both.
fn c_form_lhs() -> [(&'static str, RawLevel); 4] {
    [
        ("0", RawLevel::Zero),
        ("1", raw_succ(RawLevel::Zero)),
        ("max u v", raw_max(RawLevel::Param(0), RawLevel::Param(1))),
        ("max v u", raw_max(RawLevel::Param(1), RawLevel::Param(0))),
    ]
}

fn imax_max_u_v(a: RawLevel) -> RawLevel {
    raw_imax(a, raw_max(RawLevel::Param(0), RawLevel::Param(1)))
}

fn succ_imax_max_u_v(a: RawLevel) -> RawLevel {
    raw_succ(imax_max_u_v(a))
}

/// Refused as written, under a written `succ`, and inside a `max` (where
/// instantiating the other side can leave it alone at the top of a sort).
#[test]
fn test_validate_imax_reducing_to_max_is_refused_wherever_written() {
    for (a, lhs) in c_form_lhs() {
        let alone = imax_max_u_v(lhs.clone());
        for l in [
            alone.clone(),
            raw_succ(alone.clone()),
            raw_max(RawLevel::Param(2), alone),
        ] {
            assert_eq!(
                sort(l.clone(), 3),
                refused_as(WrittenLevel::IMaxReducingToMax),
                "a = {a}: {l:?}"
            );
        }
        let succ_form = lean::from_raw(&succ_imax_max_u_v(lhs));
        assert!(
            !lean::is_geq(&succ_form, &lean::from_raw(&RawLevel::Param(0))),
            "a = {a}: the port keeps succ (max u v)"
        );
    }
}

/// Controls: the forms Lean's elaborator writes, which validation admits.
/// `succ (imax u v)` is `Eq.{imax u v + 1}` in `implies_congr`.
#[test]
fn test_validate_control_levels_lean_writes_are_admitted() {
    for (l, arity) in [
        (
            raw_succ(raw_imax(RawLevel::Param(0), RawLevel::Param(1))),
            2,
        ),
        (raw_imax(RawLevel::Param(0), RawLevel::Param(1)), 2),
        (raw_max(raw_succ(RawLevel::Zero), RawLevel::Param(0)), 1),
        (RawLevel::Zero, 0),
        (raw_max(RawLevel::Param(0), RawLevel::Zero), 1),
    ] {
        sort(l.clone(), arity).unwrap_or_else(|e| panic!("{l:?} refused: {e}"));
    }
}

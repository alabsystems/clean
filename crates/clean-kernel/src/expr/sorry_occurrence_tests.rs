// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A sorry is ANY occurrence of `sorryAx` / `sorry`, whatever its arguments.
//!
//! Before 2026-09-28 the recognizers in `sorry.rs` matched `sorryAx` only as
//! `@sorryAx α b` with `b` literally `true` / `false`, so each shape below
//! except the two literal controls read as sorry-FREE, and `clean check`
//! passed `theorem bad : False := @sorryAx False (!true)` with
//! `sorry_axioms: 0`. Every negative assertion here is a shape that used to
//! pass; every positive control is a shape that was always recognised.

use super::super::{BinderInfo, Expr, MDataMap};
use crate::level::Level;
use crate::name::Name;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn sorry_ax() -> Expr {
    Expr::const_(Name::from_string("sorryAx"), vec![Level::zero()])
}

/// The legacy `sorry` constant. `#[cfg(test)]` at module root so the
/// production sorry-bypass lint (`cmd_replacement/sorry_bypass_lint.rs`) reads
/// this direct construction as the test fixture it is.
#[cfg(test)]
fn legacy_sorry() -> Expr {
    Expr::const_(Name::from_string("sorry"), vec![Level::zero()])
}

fn falso() -> Expr {
    c("False")
}

/// `!true`, the reviewer's flag: `not true` — not a literal.
fn not_true() -> Expr {
    Expr::app(c("not"), c("Bool.true"))
}

/// `decide False`, the coerced-proposition flag.
fn decide_false() -> Expr {
    Expr::apps(c("Decidable.decide"), [falso(), c("instDecidableFalse")])
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

/// (has_sorry, has_explicit, has_synthetic, occurrences)
fn scan(e: &Expr) -> (bool, bool, bool, usize) {
    let (has, explicit, synthetic) = e.sorry_scan();
    (has, explicit, synthetic, e.count_sorry_occurrences())
}

#[test]
fn non_literal_flag_is_a_sorry() {
    let bad = Expr::apps(sorry_ax(), [falso(), not_true()]);
    assert!(bad.is_sorry(), "@sorryAx False (!true) is a sorry");
    assert!(bad.is_non_synthetic_sorry());
    assert!(
        !bad.is_synthetic_sorry(),
        "only a literal `true` is synthetic"
    );
    assert_eq!(scan(&bad), (true, true, false, 1));
    let (explicit, synthetic, _, _) = bad.trust_scan();
    assert!(explicit && !synthetic);
}

#[test]
fn decide_coerced_flag_is_a_sorry() {
    let bad = Expr::apps(sorry_ax(), [falso(), decide_false()]);
    assert!(bad.has_sorry());
    assert_eq!(scan(&bad), (true, true, false, 1));
}

#[test]
fn partial_application_is_a_sorry() {
    let partial = Expr::app(sorry_ax(), falso());
    assert!(partial.is_sorry(), "`sorryAx False` (no flag) is a sorry");
    assert_eq!(scan(&partial), (true, true, false, 1));
}

#[test]
fn bare_constant_is_a_sorry() {
    let bare = sorry_ax();
    assert!(bare.is_sorry());
    assert_eq!(scan(&bare), (true, true, false, 1));
    // As the ARGUMENT of another function (`def mysorry := @sorryAx` passes
    // it along): the walk reaches it as its own node.
    let passed_along = Expr::app(c("id"), sorry_ax());
    assert_eq!(scan(&passed_along), (true, true, false, 1));
}

#[test]
fn eta_expanded_sorry_under_a_binder_is_a_sorry() {
    // fun (b : Bool) => @sorryAx False b   (flag is a bound variable)
    let eta = lam(c("Bool"), Expr::apps(sorry_ax(), [falso(), Expr::bvar(0)]));
    assert_eq!(scan(&eta), (true, true, false, 1));
    // ... applied: (fun b => @sorryAx False b) true
    let applied = Expr::app(eta, c("Bool.true"));
    assert_eq!(scan(&applied), (true, true, false, 1));
}

#[test]
fn sorry_in_a_let_value_is_a_sorry() {
    // let f := @sorryAx False; f (!true)
    let f = Expr::app(sorry_ax(), falso());
    let body = Expr::app(Expr::bvar(0), not_true());
    let e = Expr::let_named(
        Name::from_string("f"),
        Expr::arrow(c("Bool"), falso()),
        f,
        body,
        false,
    );
    assert_eq!(scan(&e), (true, true, false, 1));
}

#[test]
fn sorry_behind_mdata_is_a_sorry() {
    let head = Expr::mdata(MDataMap::new(), sorry_ax());
    let e = Expr::apps(head, [falso(), not_true()]);
    assert!(e.has_sorry(), "an MData-wrapped head still names sorryAx");
    assert_eq!(e.count_sorry_occurrences(), 1);
}

#[test]
fn sorry_in_a_type_position_is_a_sorry() {
    // Pi (h : @sorryAx Prop (!true)), False
    let ty = Expr::apps(
        Expr::const_(
            Name::from_string("sorryAx"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::prop(), not_true()],
    );
    let pi = Expr::pi(BinderInfo::Default, ty, falso());
    assert_eq!(scan(&pi), (true, true, false, 1));
}

#[test]
fn extra_arguments_keep_the_flag_position() {
    // @sorryAx (Nat -> False) true 0 : synthetic, ONE occurrence.
    let e = Expr::apps(
        sorry_ax(),
        [
            Expr::arrow(c("Nat"), falso()),
            c("Bool.true"),
            c("Nat.zero"),
        ],
    );
    assert!(e.is_synthetic_sorry());
    assert_eq!(scan(&e), (true, false, true, 1));
}

#[test]
fn a_sorry_hidden_in_a_sorry_argument_is_counted() {
    // @sorryAx False (@sorryAx Bool true): two occurrences, both kinds.
    let inner = Expr::apps(sorry_ax(), [c("Bool"), c("Bool.true")]);
    let outer = Expr::apps(sorry_ax(), [falso(), inner]);
    assert_eq!(scan(&outer), (true, true, true, 2));
}

#[test]
fn literal_controls_are_unchanged() {
    let explicit = Expr::apps(sorry_ax(), [falso(), c("Bool.false")]);
    assert!(explicit.is_non_synthetic_sorry() && !explicit.is_synthetic_sorry());
    assert_eq!(scan(&explicit), (true, true, false, 1));
    let synthetic = Expr::apps(sorry_ax(), [falso(), c("Bool.true")]);
    assert!(synthetic.is_synthetic_sorry() && !synthetic.is_non_synthetic_sorry());
    assert_eq!(scan(&synthetic), (true, false, true, 1));
    // One spine is ONE occurrence: its partial prefix `sorryAx False` is not
    // a second, flag-less sorry.
    let (explicit_flag, synthetic_flag, _, _) = synthetic.trust_scan();
    assert!(!explicit_flag && synthetic_flag);
    let legacy = Expr::app(legacy_sorry(), falso());
    assert_eq!(scan(&legacy), (true, true, false, 1));
}

#[test]
fn sorry_free_terms_stay_sorry_free() {
    let e = lam(c("Bool"), Expr::apps(c("ite"), [falso(), Expr::bvar(0)]));
    assert_eq!(scan(&e), (false, false, false, 0));
    // A constant whose name merely CONTAINS "sorry" is not the axiom.
    assert!(!c("sorryAxiomLemma").has_sorry());
    assert!(!c("my.sorry").has_sorry());
}

#[test]
fn trusted_markers_are_counted_in_any_position() {
    let trusted = Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]);
    // Bare, as an argument, partially applied: each one reference.
    let e = Expr::app(c("id"), trusted.clone());
    assert_eq!(e.trust_scan(), (false, false, 0, 1));
    let e = Expr::app(trusted, falso());
    assert_eq!(e.trust_scan(), (false, false, 0, 1));
}

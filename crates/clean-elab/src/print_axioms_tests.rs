// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit pins for the pure parts of `#print axioms`. The census itself is
//! pinned through the elaborator in `tests/guard_commands_e2e.rs`.

use super::*;
use clean_kernel::BinderInfo;

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

fn names(e: &Expr) -> Vec<String> {
    used_constants_in_order(e)
        .iter()
        .map(ToString::to_string)
        .collect()
}

#[test]
fn test_used_constants_in_order_application_visits_function_first() {
    // `f (g a) a b`: f, then the first argument's g and a, then b; a once.
    let e = Expr::app(
        Expr::app(Expr::app(c("f"), Expr::app(c("g"), c("a"))), c("a")),
        c("b"),
    );
    assert_eq!(names(&e), ["f", "g", "a", "b"]);
}

#[test]
fn test_used_constants_in_order_binder_domain_before_body() {
    let e = Expr::pi(
        BinderInfo::Default,
        c("Dom"),
        Expr::app(c("Body"), Expr::bvar(0)),
    );
    assert_eq!(names(&e), ["Dom", "Body"]);
}

#[test]
fn test_used_constants_in_order_projection_skips_structure_name() {
    let e = Expr::proj(Name::from_string("Prod"), 0, c("p"));
    assert_eq!(names(&e), ["p"]);
}

#[test]
fn test_axioms_message_without_axioms_returns_lean_text() {
    assert_eq!(
        axioms_message(&Name::from_string("t"), &[]),
        "'t' does not depend on any axioms"
    );
}

#[test]
fn test_axioms_message_over_width_breaks_every_separator() {
    // Lean's `sbracket` group: flat up to 120 columns, else every `,`+line
    // breaks to the group's one-column nest.
    let axioms: Vec<Name> = ["propext", "Classical.choice", "Quot.sound"]
        .iter()
        .map(|s| Name::from_string(s))
        .collect();
    let fits = Name::from_string(
        &"x".repeat(120 - "'' depends on axioms: [propext, Classical.choice, Quot.sound]".len()),
    );
    let flat = axioms_message(&fits, &axioms);
    assert_eq!(flat.chars().count(), 120);
    assert!(!flat.contains('\n'), "{flat}");
    let long =
        Name::from_string(&"x".repeat(
            1 + 120 - "'' depends on axioms: [propext, Classical.choice, Quot.sound]".len(),
        ));
    assert!(
        axioms_message(&long, &axioms).ends_with("[propext,\n Classical.choice,\n Quot.sound]"),
        "{}",
        axioms_message(&long, &axioms)
    );
}

#[test]
fn test_lean_name_to_string_escapes_non_identifier_components() {
    let plain = Name::from_string("TrustIr.ay_sound_unsat");
    assert_eq!(lean_name_to_string(&plain), "TrustIr.ay_sound_unsat");
    let odd = Name::anon().str("Foo").str("a b");
    assert_eq!(lean_name_to_string(&odd), "Foo.«a b»");
    // Greek letters are identifier characters in Lean 4.8.0; Latin-1 is not yet.
    assert_eq!(lean_name_to_string(&Name::anon().str("α")), "α");
    assert_eq!(lean_name_to_string(&Name::anon().str("é")), "«é»");
}

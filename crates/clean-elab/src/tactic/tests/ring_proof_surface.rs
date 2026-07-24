// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct tests for the shared carrier theorem surface behind ring proof replay.

use super::super::ring_proof_surface::{
    assoc_name, comm_name, distribution_entry, identity_entries, is_identity_expr, zero_const_name,
    IdentityKind,
};
use clean_kernel::name::Name;
use clean_kernel::Expr;

fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_ring_proof_surface_lookup_names_cover_rat_and_existing_carriers() {
    assert_eq!(assoc_name("Rat.add"), Some("Rat.add_assoc"));
    assert_eq!(assoc_name("Rat.mul"), Some("Rat.mul_assoc"));
    assert_eq!(comm_name("Rat.add"), Some("Rat.add_comm"));
    assert_eq!(comm_name("Rat.mul"), Some("Rat.mul_comm"));

    assert_eq!(assoc_name("Int.add"), Some("Int.add_assoc"));
    assert_eq!(comm_name("Int.mul"), Some("Int.mul_comm"));
    assert_eq!(assoc_name("Foo.add"), None);
    assert_eq!(comm_name("Foo.mul"), None);
}

#[test]
fn test_ring_proof_surface_rat_identity_entries_cover_units_and_annihilators() {
    let add_entries = identity_entries("Rat.add");
    assert_eq!(
        add_entries.len(),
        2,
        "Rat.add should expose zero identities"
    );
    assert_eq!(add_entries[0].lemma, "Rat.add_zero");
    assert!(add_entries[0].id_on_right);
    assert!(matches!(add_entries[0].kind, IdentityKind::Zero));
    assert!(!add_entries[0].annihilator);
    assert_eq!(add_entries[1].lemma, "Rat.zero_add");
    assert!(!add_entries[1].id_on_right);
    assert!(matches!(add_entries[1].kind, IdentityKind::Zero));
    assert!(!add_entries[1].annihilator);

    let mul_entries = identity_entries("Rat.mul");
    assert_eq!(
        mul_entries.len(),
        4,
        "Rat.mul should expose one/zero identities plus annihilators"
    );
    assert_eq!(mul_entries[0].lemma, "Rat.mul_one");
    assert!(matches!(mul_entries[0].kind, IdentityKind::One));
    assert_eq!(mul_entries[1].lemma, "Rat.one_mul");
    assert!(matches!(mul_entries[1].kind, IdentityKind::One));
    assert_eq!(mul_entries[2].lemma, "Rat.mul_zero");
    assert!(mul_entries[2].annihilator);
    assert_eq!(mul_entries[3].lemma, "Rat.zero_mul");
    assert!(mul_entries[3].annihilator);
}

#[test]
fn test_ring_proof_surface_rat_distribution_and_zero_constants_are_registered() {
    let distrib = distribution_entry("Rat.mul").expect("Rat.mul should distribute over Rat.add");
    assert_eq!(distrib.left_distrib, "Rat.left_distrib");
    assert_eq!(distrib.right_distrib, "Rat.right_distrib");
    assert_eq!(distrib.sum_op, "Rat.add");

    assert_eq!(zero_const_name("Rat.add"), Some("Rat.zero"));
    assert_eq!(zero_const_name("Rat.mul"), Some("Rat.zero"));
    assert!(distribution_entry("Rat.add").is_none());
}

#[test]
fn test_ring_proof_surface_identity_detection_matches_rat_and_int_constants() {
    let rat_zero = const_expr("Rat.zero");
    let rat_one = const_expr("Rat.one");
    let int_zero = const_expr("Int.zero");

    assert!(is_identity_expr(&rat_zero, "Rat.add", IdentityKind::Zero));
    assert!(is_identity_expr(&rat_zero, "Rat.mul", IdentityKind::Zero));
    assert!(is_identity_expr(&rat_one, "Rat.mul", IdentityKind::One));
    assert!(!is_identity_expr(&rat_one, "Rat.add", IdentityKind::Zero));

    assert!(is_identity_expr(&int_zero, "Int.add", IdentityKind::Zero));
    assert!(!is_identity_expr(&int_zero, "Rat.add", IdentityKind::Zero));
}

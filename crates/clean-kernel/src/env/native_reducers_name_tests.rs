// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;

fn anon_expr() -> Expr {
    Expr::const_(Name::from_string("Lean.Name.anonymous"), vec![])
}

fn str_expr(parent: Expr, s: &str) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Lean.Name.str"), vec![]),
            parent,
        ),
        Expr::str_lit(s),
    )
}

fn num_expr(parent: Expr, n: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Lean.Name.num"), vec![]),
            parent,
        ),
        Expr::nat_lit(n),
    )
}

fn bool_expr(b: bool) -> Expr {
    Expr::const_(
        Name::from_string(if b { "Bool.true" } else { "Bool.false" }),
        vec![],
    )
}

fn nested_name() -> Name {
    Name::anon().str("foo").num(7).str("bar")
}

fn nested_name_expr() -> Expr {
    str_expr(num_expr(str_expr(anon_expr(), "foo"), 7), "bar")
}

fn assert_name_result(result: Option<Expr>, expected: Name) {
    let result = result.expect("expected reducer to produce a Lean.Name expression");
    assert_eq!(get_name_val(&result), Some(expected));
}

fn assert_bool_result(result: Option<Expr>, expected: bool) {
    let result = result.expect("expected reducer to produce a Bool expression");
    assert_eq!(get_bool_val(&result), Some(expected));
}

fn nat_lit_value(result: Option<Expr>) -> u64 {
    let result = result.expect("expected reducer to produce a Nat literal");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64().expect("Nat literal should fit in u64"),
        _ => panic!("expected Nat literal, got {:?}", result),
    }
}

fn string_lit_value(result: Option<Expr>) -> String {
    let result = result.expect("expected reducer to produce a String literal");
    match result.kind() {
        ExprKind::Lit(Literal::String(s)) => s.to_string(),
        _ => panic!("expected String literal, got {:?}", result),
    }
}

#[test]
fn test_get_name_val_anonymous() {
    assert_eq!(get_name_val(&anon_expr()), Some(Name::anon()));
}

#[test]
fn test_get_name_val_str() {
    let expr = str_expr(anon_expr(), "foo");
    assert_eq!(get_name_val(&expr), Some(Name::anon().str("foo")));
}

#[test]
fn test_get_name_val_num() {
    let expr = num_expr(anon_expr(), 42);
    assert_eq!(get_name_val(&expr), Some(Name::anon().num(42)));
}

#[test]
fn test_get_name_val_nested() {
    assert_eq!(get_name_val(&nested_name_expr()), Some(nested_name()));
}

#[test]
fn test_mk_name_expr_roundtrip_anonymous() {
    let name = Name::anon();
    let expr = mk_name_expr(&name);
    assert_eq!(get_name_val(&expr), Some(name));
}

#[test]
fn test_mk_name_expr_roundtrip_nested() {
    let name = Name::anon().str("pkg").str("module").num(3).str("decl");
    let expr = mk_name_expr(&name);
    assert_eq!(get_name_val(&expr), Some(name));
}

#[test]
fn test_reduce_name_mk_str_basic() {
    let parent = anon_expr();
    let s = Expr::str_lit("foo");
    assert_name_result(reduce_name_mk_str(&[&parent, &s]), Name::anon().str("foo"));
}

#[test]
fn test_reduce_name_mk_str_nested_parent() {
    let parent = num_expr(str_expr(anon_expr(), "foo"), 7);
    let s = Expr::str_lit("bar");
    assert_name_result(
        reduce_name_mk_str(&[&parent, &s]),
        Name::anon().str("foo").num(7).str("bar"),
    );
}

#[test]
fn test_reduce_name_mk_str_insufficient_args() {
    let parent = nested_name_expr();
    assert!(reduce_name_mk_str(&[&parent]).is_none());
}

#[test]
fn test_reduce_name_mk_str_non_literal_returns_none() {
    let parent = Expr::const_(Name::from_string("x"), vec![]);
    let s = Expr::str_lit("bar");
    let bad_s = Expr::nat_lit(5);
    assert!(reduce_name_mk_str(&[&parent, &s]).is_none());
    assert!(reduce_name_mk_str(&[&anon_expr(), &bad_s]).is_none());
}

#[test]
fn test_reduce_name_mk_num_basic() {
    let parent = anon_expr();
    let n = Expr::nat_lit(9);
    assert_name_result(reduce_name_mk_num(&[&parent, &n]), Name::anon().num(9));
}

#[test]
fn test_reduce_name_mk_num_nested_parent() {
    let parent = str_expr(anon_expr(), "foo");
    let n = Expr::nat_lit(17);
    assert_name_result(
        reduce_name_mk_num(&[&parent, &n]),
        Name::anon().str("foo").num(17),
    );
}

#[test]
fn test_reduce_name_mk_num_insufficient_args() {
    let parent = str_expr(anon_expr(), "foo");
    assert!(reduce_name_mk_num(&[&parent]).is_none());
}

#[test]
fn test_reduce_name_beq_equal() {
    let a = nested_name_expr();
    let b = mk_name_expr(&nested_name());
    assert_bool_result(reduce_name_beq(&[&a, &b]), true);
}

#[test]
fn test_reduce_name_beq_not_equal() {
    let a = nested_name_expr();
    let b = str_expr(num_expr(str_expr(anon_expr(), "foo"), 8), "bar");
    assert_bool_result(reduce_name_beq(&[&a, &b]), false);
}

#[test]
fn test_reduce_name_beq_both_anonymous() {
    let a = anon_expr();
    let b = anon_expr();
    assert_bool_result(reduce_name_beq(&[&a, &b]), true);
}

#[test]
fn test_reduce_name_beq_nested_equal() {
    let a = str_expr(num_expr(str_expr(anon_expr(), "alpha"), 2), "mathverse");
    let b = str_expr(num_expr(str_expr(anon_expr(), "alpha"), 2), "mathverse");
    assert_bool_result(reduce_name_beq(&[&a, &b]), true);
}

#[test]
fn test_reduce_name_hash_produces_nat() {
    let name = nested_name();
    let expr = mk_name_expr(&name);
    let hash = nat_lit_value(reduce_name_hash(&[&expr]));
    assert_eq!(hash, lean4_name_hash(&name));
}

#[test]
fn test_reduce_name_hash_equal_names_same_hash() {
    let a = nested_name_expr();
    let b = mk_name_expr(&nested_name());
    let hash_a = nat_lit_value(reduce_name_hash(&[&a]));
    let hash_b = nat_lit_value(reduce_name_hash(&[&b]));
    assert_eq!(hash_a, hash_b);
}

#[test]
fn test_reduce_name_hash_different_names() {
    let name_a = Name::anon().str("foo").num(7).str("bar");
    let name_b = Name::anon().str("foo").num(8).str("bar");
    let expr_a = mk_name_expr(&name_a);
    let expr_b = mk_name_expr(&name_b);
    let hash_a = nat_lit_value(reduce_name_hash(&[&expr_a]));
    let hash_b = nat_lit_value(reduce_name_hash(&[&expr_b]));
    assert_eq!(hash_a, lean4_name_hash(&name_a));
    assert_eq!(hash_b, lean4_name_hash(&name_b));
    assert_ne!(hash_a, hash_b);
}

#[test]
fn test_reduce_name_to_string_simple() {
    let name = str_expr(anon_expr(), "foo");
    assert_eq!(
        string_lit_value(reduce_name_to_string(&[&name, &bool_expr(true)])),
        "foo"
    );
}

#[test]
fn test_reduce_name_to_string_dotted_with_sep_true() {
    let name = nested_name_expr();
    assert_eq!(
        string_lit_value(reduce_name_to_string(&[&name, &bool_expr(true)])),
        "foo.7.bar"
    );
}

#[test]
fn test_reduce_name_to_string_with_sep_false() {
    let name = nested_name_expr();
    assert_eq!(
        string_lit_value(reduce_name_to_string(&[&name, &bool_expr(false)])),
        "foo7bar"
    );
}

#[test]
fn test_reduce_name_append_basic() {
    let prefix = str_expr(anon_expr(), "foo");
    let suffix = str_expr(anon_expr(), "bar");
    assert_name_result(
        reduce_name_append(&[&prefix, &suffix]),
        Name::anon().str("foo").str("bar"),
    );
}

#[test]
fn test_reduce_name_append_to_anonymous_suffix() {
    let prefix = nested_name_expr();
    let suffix = anon_expr();
    assert_name_result(reduce_name_append(&[&prefix, &suffix]), nested_name());
}

#[test]
fn test_reduce_name_append_from_anonymous_prefix() {
    let prefix = anon_expr();
    let suffix = num_expr(str_expr(anon_expr(), "tail"), 3);
    assert_name_result(
        reduce_name_append(&[&prefix, &suffix]),
        Name::anon().str("tail").num(3),
    );
}

#[test]
fn test_reduce_name_append_nested() {
    let prefix = num_expr(str_expr(anon_expr(), "left"), 1);
    let suffix = num_expr(str_expr(anon_expr(), "right"), 2);
    assert_name_result(
        reduce_name_append(&[&prefix, &suffix]),
        Name::anon().str("left").num(1).str("right").num(2),
    );
}

#[test]
fn test_name_native_reducers_registered() {
    let mut env = Environment::new();
    env.init_name_native_reducers();

    assert!(
        env.get_native_reducer(&names::LEAN_NAME_MK_STR).is_some(),
        "Lean.Name.mkStr reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LEAN_NAME_MK_NUM).is_some(),
        "Lean.Name.mkNum reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LEAN_NAME_BEQ).is_some(),
        "Lean.Name.beq reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LEAN_NAME_HASH).is_some(),
        "Lean.Name.hash reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LEAN_NAME_TO_STRING)
            .is_some(),
        "Lean.Name.toString reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LEAN_NAME_APPEND).is_some(),
        "Lean.Name.append reducer should be registered"
    );
}

#[test]
fn test_empty_args_return_none_for_each_reducer() {
    assert!(reduce_name_mk_str(&[]).is_none());
    assert!(reduce_name_mk_num(&[]).is_none());
    assert!(reduce_name_beq(&[]).is_none());
    assert!(reduce_name_hash(&[]).is_none());
    assert!(reduce_name_to_string(&[]).is_none());
    assert!(reduce_name_append(&[]).is_none());
}

// --- Lean 4 Name.hash compatibility tests (Part of #3249) ---
// Cross-validated against Lean 4's C implementation:
//   - lean_uint64_mix_hash (lean.h:2026, hash.h:15)
//   - lean_string_hash = MurmurHash64A(bytes, len, 11) (object.cpp:2412)
//   - Name.hash (Init/Prelude.lean:4714-4717)

#[test]
fn test_name_hash_anonymous_is_lean4_sentinel() {
    let name = Name::anon();
    assert_eq!(
        name.lean4_hash(),
        1723,
        "anonymous Name hash should be Lean 4 sentinel 1723"
    );
}

#[test]
fn test_name_hash_uses_lean4_hash_via_reducer() {
    let name = Name::anon().str("Nat").str("add");
    let expr = mk_name_expr(&name);
    let hash_from_reducer = nat_lit_value(reduce_name_hash(&[&expr]));
    assert_eq!(
        hash_from_reducer,
        name.lean4_hash(),
        "Name hash reducer should match Name::lean4_hash()"
    );
}

#[test]
fn test_name_hash_consistency_str_then_num() {
    let a = Name::anon().str("foo").num(42);
    let b = Name::anon().str("foo").num(42);
    assert_eq!(
        a.lean4_hash(),
        b.lean4_hash(),
        "Equal names should have equal Lean 4 hashes"
    );
}

#[test]
fn test_name_hash_differs_for_different_components() {
    let a = Name::anon().str("foo");
    let b = Name::anon().str("bar");
    assert_ne!(
        a.lean4_hash(),
        b.lean4_hash(),
        "Different names should have different hashes"
    );
}

// --- Lean 4 cross-validated Name.hash reference values (Part of #3249) ---
// These exact values are computed from Lean 4's C implementation:
//   Name.hash(anonymous) = 1723
//   Name.hash(str p s) = mixHash(p.hash, String.hash(s))
//   Name.hash(num p v) = mixHash(p.hash, v)
// where String.hash = MurmurHash64A(bytes, 11) and mixHash = lean_uint64_mix_hash.

#[test]
fn test_name_hash_lean4_reference_nat() {
    let name = Name::anon().str("Nat");
    assert_eq!(
        name.lean4_hash(),
        11442535297760353691,
        "Name.hash(Nat) must match Lean 4 reference"
    );
}

#[test]
fn test_name_hash_lean4_reference_nat_add() {
    let name = Name::anon().str("Nat").str("add");
    assert_eq!(
        name.lean4_hash(),
        17073733886952259026,
        "Name.hash(Nat.add) must match Lean 4 reference"
    );
}

#[test]
fn test_name_hash_lean4_reference_list() {
    let name = Name::anon().str("List");
    assert_eq!(
        name.lean4_hash(),
        9582258842178272501,
        "Name.hash(List) must match Lean 4 reference"
    );
}

#[test]
fn test_name_hash_lean4_reference_list_map() {
    let name = Name::anon().str("List").str("map");
    assert_eq!(
        name.lean4_hash(),
        3191694513845892602,
        "Name.hash(List.map) must match Lean 4 reference"
    );
}

#[test]
fn test_name_hash_lean4_reference_numeric() {
    let name = Name::anon().num(42);
    assert_eq!(
        name.lean4_hash(),
        16436471498770525538,
        "Name.hash(anonymous.42) must match Lean 4 reference"
    );
}

#[test]
fn test_name_hash_lean4_reference_nested_foo_7_bar() {
    let name = Name::anon().str("foo").num(7).str("bar");
    assert_eq!(
        name.lean4_hash(),
        7920425898089674939,
        "Name.hash(foo.7.bar) must match Lean 4 reference"
    );
}

#[test]
fn test_name_hash_lean4_reference_via_reducer_nat_add() {
    // Verify the native reducer produces the exact Lean 4 value
    let name = Name::anon().str("Nat").str("add");
    let expr = mk_name_expr(&name);
    let hash = nat_lit_value(reduce_name_hash(&[&expr]));
    assert_eq!(
        hash, 17073733886952259026,
        "Name.hash reducer for Nat.add must match Lean 4 reference"
    );
}

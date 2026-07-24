// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for disjunction/conjunction proof term construction helpers.
//!
//! Covers or_chain_type, and_chain_type, extract_and_conjunct,
//! build_and_chain_from_bvars, and precompute_or_chain_suffixes for
//! chains of size 1..4, verifying right-associativity invariants and
//! de Bruijn index correctness.

use crate::bridge::disjunction::{
    and_chain_type, build_and_chain_from_bvars, extract_and_conjunct, mk_and_intro, mk_and_left,
    mk_and_right, mk_constant_or_motive, or_chain_type, precompute_or_chain_suffixes,
};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

fn mk_prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_mk_constant_or_motive_lifts_target_bvars_under_lambda() {
    let a = mk_prop("A");
    let b = mk_prop("B");
    let target = Expr::app(
        Expr::const_(Name::from_string("Goal"), vec![]),
        Expr::bvar(0),
    );

    let result = mk_constant_or_motive(&a, &b, &target);

    let or_ab = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    );
    let expected = Expr::lam(BinderInfo::Default, or_ab, target.lift(1));
    assert_eq!(result, expected);
}

// ---- or_chain_type tests ----

#[test]
fn test_or_chain_type_singleton() {
    let p = mk_prop("P");
    assert_eq!(or_chain_type(std::slice::from_ref(&p)), p);
}

#[test]
fn test_or_chain_type_pair() {
    let p = mk_prop("P");
    let q = mk_prop("Q");
    let result = or_chain_type(&[p.clone(), q.clone()]);
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p),
        q,
    );
    assert_eq!(result, expected);
}

#[test]
fn test_or_chain_type_triple_is_right_associative() {
    let p = mk_prop("P");
    let q = mk_prop("Q");
    let r = mk_prop("R");
    // Expected: Or P (Or Q R)
    let qr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), q),
        r,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p),
        qr,
    );
    assert_eq!(
        or_chain_type(&[mk_prop("P"), mk_prop("Q"), mk_prop("R")]),
        expected
    );
}

#[test]
fn test_or_chain_type_quad_is_right_associative() {
    let props: Vec<Expr> = ["A", "B", "C", "D"].into_iter().map(mk_prop).collect();
    let result = or_chain_type(&props);
    // Expected: Or A (Or B (Or C D))
    let cd = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), mk_prop("C")),
        mk_prop("D"),
    );
    let bcd = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), mk_prop("B")),
        cd,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), mk_prop("A")),
        bcd,
    );
    assert_eq!(result, expected);
}

// ---- and_chain_type tests ----

#[test]
fn test_and_chain_type_singleton() {
    let p = mk_prop("P");
    assert_eq!(and_chain_type(std::slice::from_ref(&p)), p);
}

#[test]
fn test_and_chain_type_triple_is_right_associative() {
    let p = mk_prop("P");
    let q = mk_prop("Q");
    let r = mk_prop("R");
    let qr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), q),
        r,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p),
        qr,
    );
    assert_eq!(
        and_chain_type(&[mk_prop("P"), mk_prop("Q"), mk_prop("R")]),
        expected
    );
}

// ---- extract_and_conjunct tests ----

#[test]
fn test_extract_and_conjunct_singleton() {
    let h = mk_prop("proof_of_P");
    // total=1, position=0: no And wrapper, return h directly.
    let result = extract_and_conjunct(&h, 0, 1);
    assert_eq!(result, h);
}

#[test]
fn test_extract_and_conjunct_pair_first() {
    let h = mk_prop("proof_of_and");
    // total=2, position=0: And.left h
    let result = extract_and_conjunct(&h, 0, 2);
    assert_eq!(result, mk_and_left(&h));
}

#[test]
fn test_extract_and_conjunct_pair_second() {
    let h = mk_prop("proof_of_and");
    // total=2, position=1: And.right h (innermost, no And.left)
    let result = extract_and_conjunct(&h, 1, 2);
    assert_eq!(result, mk_and_right(&h));
}

#[test]
fn test_extract_and_conjunct_triple_all_positions() {
    // h : And A (And B C)
    let h = mk_prop("proof_of_and_chain");

    // position=0: And.left h
    let pos0 = extract_and_conjunct(&h, 0, 3);
    assert_eq!(pos0, mk_and_left(&h));

    // position=1: And.left (And.right h)
    let pos1 = extract_and_conjunct(&h, 1, 3);
    let right_h = mk_and_right(&h);
    assert_eq!(pos1, mk_and_left(&right_h));

    // position=2: And.right (And.right h) (innermost)
    let pos2 = extract_and_conjunct(&h, 2, 3);
    assert_eq!(pos2, mk_and_right(&right_h));
}

#[test]
fn test_extract_and_conjunct_quad_all_positions() {
    // h : And A (And B (And C D))
    let h = mk_prop("proof_of_quad_and");

    let pos0 = extract_and_conjunct(&h, 0, 4);
    assert_eq!(pos0, mk_and_left(&h), "position 0: And.left h");

    let r1 = mk_and_right(&h);
    let pos1 = extract_and_conjunct(&h, 1, 4);
    assert_eq!(pos1, mk_and_left(&r1), "position 1: And.left (And.right h)");

    let r2 = mk_and_right(&r1);
    let pos2 = extract_and_conjunct(&h, 2, 4);
    assert_eq!(
        pos2,
        mk_and_left(&r2),
        "position 2: And.left (And.right (And.right h))"
    );

    let pos3 = extract_and_conjunct(&h, 3, 4);
    assert_eq!(
        pos3,
        mk_and_right(&r2),
        "position 3: And.right (And.right (And.right h))"
    );
}

// ---- build_and_chain_from_bvars tests ----

#[test]
fn test_build_and_chain_from_bvars_single() {
    let conjuncts = vec![mk_prop("A")];
    let result = build_and_chain_from_bvars(&conjuncts, 0, 1);
    assert_eq!(result, Expr::bvar(0));
}

#[test]
fn test_build_and_chain_from_bvars_pair() {
    let conjuncts = vec![mk_prop("A"), mk_prop("B")];
    // bvar(1)=A, bvar(0)=B → And.intro A B bvar(1) bvar(0)
    let result = build_and_chain_from_bvars(&conjuncts, 0, 2);
    let expected = mk_and_intro(&mk_prop("A"), &mk_prop("B"), &Expr::bvar(1), &Expr::bvar(0));
    assert_eq!(result, expected);
}

#[test]
fn test_build_and_chain_from_bvars_triple() {
    let conjuncts = vec![mk_prop("A"), mk_prop("B"), mk_prop("C")];
    // bvar(2)=A, bvar(1)=B, bvar(0)=C
    // Inner: And.intro B C bvar(1) bvar(0)
    // Outer: And.intro A (And B C) bvar(2) inner
    let result = build_and_chain_from_bvars(&conjuncts, 0, 3);
    let bc_type = and_chain_type(&[mk_prop("B"), mk_prop("C")]);
    let inner = mk_and_intro(&mk_prop("B"), &mk_prop("C"), &Expr::bvar(1), &Expr::bvar(0));
    let expected = mk_and_intro(&mk_prop("A"), &bc_type, &Expr::bvar(2), &inner);
    assert_eq!(result, expected);
}

#[test]
fn test_build_and_chain_from_bvars_quad() {
    let conjuncts = vec![mk_prop("A"), mk_prop("B"), mk_prop("C"), mk_prop("D")];
    // bvar(3)=A, bvar(2)=B, bvar(1)=C, bvar(0)=D
    let result = build_and_chain_from_bvars(&conjuncts, 0, 4);

    // Bottom-up construction:
    let cd = mk_and_intro(&mk_prop("C"), &mk_prop("D"), &Expr::bvar(1), &Expr::bvar(0));
    let cd_type = and_chain_type(&[mk_prop("C"), mk_prop("D")]);
    let bcd = mk_and_intro(&mk_prop("B"), &cd_type, &Expr::bvar(2), &cd);
    let bcd_type = and_chain_type(&[mk_prop("B"), mk_prop("C"), mk_prop("D")]);
    let expected = mk_and_intro(&mk_prop("A"), &bcd_type, &Expr::bvar(3), &bcd);
    assert_eq!(result, expected);
}

// ---- precompute_or_chain_suffixes tests ----

#[test]
fn test_precompute_or_chain_suffixes_empty() {
    let result = precompute_or_chain_suffixes(&[]);
    assert!(result.is_empty());
}

#[test]
fn test_precompute_or_chain_suffixes_matches_or_chain_type() {
    let props: Vec<Expr> = ["A", "B", "C", "D"].into_iter().map(mk_prop).collect();
    let suffixes = precompute_or_chain_suffixes(&props);
    assert_eq!(suffixes.len(), 4);
    for i in 0..4 {
        assert_eq!(
            suffixes[i],
            or_chain_type(&props[i..]),
            "suffix[{i}] should equal or_chain_type(props[{i}..])"
        );
    }
}

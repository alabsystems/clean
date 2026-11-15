// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::replace_box,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_seven_sort_tags_and_all_cross_tag_pairs_match_exact_derived_equality() {
    let all = sorts();
    assert_eq!(all.len(), 7);
    for a in &all {
        for b in &all {
            sort(a, b);
        }
    }
    for (a, b) in [
        (ClauseSort::BitVec(0), ClauseSort::BitVec(1)),
        (
            ClauseSort::Float {
                eb: 0,
                sb: u32::MAX,
            },
            ClauseSort::Float {
                eb: u32::MAX,
                sb: 0,
            },
        ),
    ] {
        assert!(!sort(&a, &b).0);
    }
}
#[test]
fn complete_datatype_names_constructor_field_order_and_nested_sort_tails_are_identity() {
    let a = ClauseSort::Datatype {
        name: "λ".repeat(2000) + "TAIL",
        constructors: vec![
            ("first".into(), vec![]),
            (
                "ctor".repeat(1000),
                vec![(
                    "field".repeat(1000),
                    ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
                )],
            ),
        ],
    };
    assert!(sort(&a, &a).0);
    for field in 0..5 {
        let mut b = a.clone();
        let ClauseSort::Datatype { name, constructors } = &mut b else {
            unreachable!()
        };
        match field {
            0 => name.push('!'),
            1 => constructors.reverse(),
            2 => constructors[1].0.push('!'),
            3 => constructors[1].1[0].0.push('!'),
            _ => {
                constructors[1].1[0].1 =
                    ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Int))
            }
        };
        assert!(!sort(&a, &b).0);
    }
}
#[test]
fn empty_datatype_reference_is_raw_shape_and_never_automatically_expanded() {
    let a = ClauseSort::Datatype {
        name: "D".into(),
        constructors: vec![],
    };
    let b = sorts().pop().unwrap();
    assert!(sort(&a, &a).0);
    assert!(!sort(&a, &b).0);
    let mut c = b.clone();
    let ClauseSort::Datatype { constructors, .. } = &mut c else {
        unreachable!()
    };
    constructors[0].1.clear();
    assert!(!sort(&b, &c).0);
}
#[test]
fn deep_arrays_use_actual_iterative_comparison_without_cloning_or_recursive_equality() {
    let mut a = ClauseSort::Bool;
    for _ in 0..512 {
        a = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(a));
    }
    assert!(sort(&a, &a).0);
}
#[test]
fn every_raw_formula_field_is_identity_including_none_versus_some_empty_and_binding_order() {
    let a = sample();
    assert!(formula(&a, &a).0);
    for field in 0..9 {
        let mut b = a.clone();
        match field {
            0 => b.schema.push('!'),
            1 => b.payload.push('!'),
            2 => b.smtlib = None,
            3 => b.sort = None,
            4 => b.bindings.reverse(),
            5 => b.bindings[0].0.push('!'),
            6 => b.bindings[0].1.sort = ClauseSort::Int,
            7 => b.bindings[0].1.place = ClausePlace::Unwind,
            _ => {
                b.bindings.pop();
            }
        };
        assert!(!formula(&a, &b).0);
    }
    for which in 0..2 {
        let a = ProofFormula::new("", "");
        let mut b = a.clone();
        if which == 0 {
            b.smtlib = Some(String::new());
        } else {
            b.sort = Some(String::new());
        }
        assert!(!formula(&a, &b).0);
    }
}
#[test]
fn all_eleven_place_tags_full_unsigned_indices_and_ordered_duplicates_match_derived_eq() {
    let all = places();
    assert_eq!(all.len(), 11);
    for a in &all {
        for b in &all {
            let mut x = sample();
            x.bindings[0].1.place = *a;
            let mut y = x.clone();
            y.bindings[0].1.place = *b;
            formula(&x, &y);
        }
    }
    let a = sample();
    let mut b = a.clone();
    b.bindings.push(b.bindings[0].clone());
    assert!(!formula(&a, &b).0);
}
#[test]
fn earlier_mismatch_short_circuits_later_opaque_formula_bytes_and_sort_children() {
    let a = ProofFormula::new("first", "payload");
    let mut b = ProofFormula::new("other", "payload");
    let (_, before) = formula(&a, &b);
    b.payload = "unused".repeat(100000);
    b.bindings = sample().bindings;
    let (_, after) = formula(&a, &b);
    assert_eq!(before.events, after.events);
    let a = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool));
    let mut b = ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Bool));
    let (_, before) = sort(&a, &b);
    if let ClauseSort::Array(_, tail) = &mut b {
        *tail = Box::new(ClauseSort::Datatype {
            name: "unused".repeat(100000),
            constructors: vec![],
        });
    }
    let (_, after) = sort(&a, &b);
    assert_eq!(before.events, after.events);
}

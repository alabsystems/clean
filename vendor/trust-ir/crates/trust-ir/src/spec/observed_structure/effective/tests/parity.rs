// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_seven_declared_sort_variants_preserve_equal_and_unequal_results() {
    let sorts = [
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(32),
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        ClauseSort::Float { eb: 8, sb: 24 },
        ClauseSort::RoundingMode,
        datatype("D"),
    ];
    for sort in sorts {
        let variable = SpecVar::new("x", "opaque").with_sort(sort.clone());
        assert!(run(&variable, &sort).0.is_none());
        let other = if sort == ClauseSort::Bool {
            ClauseSort::Int
        } else {
            ClauseSort::Bool
        };
        assert_eq!(run(&variable, &other).0, Some(format!("{sort:?}")));
    }
}
#[test]
fn every_accepted_legacy_shape_keeps_mathematical_range_and_exact_width() {
    let cases = [
        ("Bool", ClauseSort::Bool),
        ("Int", ClauseSort::Int),
        ("BitVec(1)", ClauseSort::BitVec(1)),
        ("BitVec(4294967295)", ClauseSort::BitVec(u32::MAX)),
        ("-7..8", ClauseSort::Int),
        ("0..0", ClauseSort::Int),
        ("-9..-7", ClauseSort::Int),
        ("7..9", ClauseSort::Int),
    ];
    for (tag, sort) in cases {
        let variable = SpecVar::new("x", tag);
        assert_eq!(variable.effective_sort(), Some(sort.clone()));
        assert!(run(&variable, &sort).0.is_none());
        run(&variable, &ClauseSort::RoundingMode);
    }
    let huge = "1".repeat(4000) + ".." + &"2".repeat(4000);
    let variable = SpecVar::new("x", huge);
    assert_eq!(run(&variable, &ClauseSort::Bool).0, Some("Int".into()));
}
#[test]
fn unreadable_tags_stay_unknown_without_an_accepting_substitute_sort() {
    for tag in [
        "",
        " Bool",
        "bool",
        "BitVec(0)",
        "BitVec(4294967296)",
        "BitVec(-1)",
        "BitVec(+1)",
        "BitVec(01)",
        "BitVec(1)tail",
        "7..0",
        "-0..0",
        "0007..0009",
        "-0007..+0008",
        "1...2",
        "opaque",
    ] {
        let variable = SpecVar::new("x", tag);
        assert!(variable.effective_sort().is_none(), "{tag}");
        assert!(run(&variable, &ClauseSort::Bool).0.is_none());
    }
}
#[test]
fn declared_sort_priority_does_not_parse_even_a_large_contradictory_legacy_tag() {
    let short = SpecVar::new("x", "Bool").with_sort(ClauseSort::Int);
    let large = SpecVar::new("x", "9".repeat(100_000)).with_sort(ClauseSort::Int);
    let (a, left, bound_a) = run(&short, &ClauseSort::Bool);
    let (b, right, bound_b) = run(&large, &ClauseSort::Bool);
    assert_eq!(a, Some("Int".into()));
    assert_eq!(a, b);
    assert_eq!(bound_a, bound_b);
    assert_eq!(left.events, right.events);
}
#[test]
fn datatype_names_constructor_order_field_order_and_nested_sorts_match_original_equality() {
    let sort = datatype("D\nλ\"'\\");
    let variable = SpecVar::new("not read", "opaque").with_sort(sort.clone());
    let ClauseSort::Datatype { constructors, .. } = &sort else {
        unreachable!()
    };
    for binding in [
        datatype("other"),
        ClauseSort::Datatype {
            name: "D\nλ\"'\\".into(),
            constructors: constructors.iter().cloned().rev().collect(),
        },
        ClauseSort::Datatype {
            name: "D\nλ\"'\\".into(),
            constructors: vec![],
        },
    ] {
        assert_eq!(run(&variable, &binding).0, Some(format!("{sort:?}")));
    }
    assert!(run(&variable, &sort).0.is_none());
}
#[test]
fn different_tag_binding_payload_is_not_walked_or_formatted() {
    let variable = SpecVar::new("x", "Bool").with_sort(ClauseSort::Bool);
    let (small, a, cut_a) = run(&variable, &ClauseSort::Int);
    let (large, b, cut_b) = run(&variable, &nested(128, datatype(&"z".repeat(50_000))));
    assert_eq!(small, Some("Bool".into()));
    assert_eq!(small, large);
    assert_eq!(cut_a, cut_b);
    assert_eq!(a.events, b.events);
}
#[test]
fn deeply_nested_equal_and_deep_leaf_mismatch_preserve_complete_debug_text() {
    let sort = nested(96, datatype("λ"));
    let variable = SpecVar::new("x", "unreadable").with_sort(sort.clone());
    assert!(run(&variable, &sort).0.is_none());
    let binding = nested(96, ClauseSort::Bool);
    assert_eq!(run(&variable, &binding).0, Some(format!("{sort:?}")));
}
#[test]
fn carried_degenerate_widths_float_bits_and_empty_datatypes_are_not_normalized() {
    for sort in [
        ClauseSort::BitVec(0),
        ClauseSort::BitVec(u32::MAX),
        ClauseSort::Float {
            eb: 0,
            sb: u32::MAX,
        },
        ClauseSort::Datatype {
            name: String::new(),
            constructors: Vec::new(),
        },
    ] {
        let variable = SpecVar::new("x", "Bool").with_sort(sort.clone());
        assert!(run(&variable, &sort).0.is_none());
        assert_eq!(
            run(&variable, &ClauseSort::Bool).0,
            Some(format!("{sort:?}"))
        );
    }
}

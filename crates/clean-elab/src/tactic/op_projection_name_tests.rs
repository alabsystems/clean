// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{is_hetero_op_projection, name_display_eq, HETERO_OP_PROJECTIONS};
use clean_kernel::name::Name;

/// Names built every way the tree builds them, including the shapes a
/// structural comparison could get wrong: a dotted SINGLE component, an
/// empty component, numeric components, and the anonymous name.
fn corpus() -> Vec<Name> {
    vec![
        Name::anon(),
        Name::from_string("HAdd.hAdd"),
        Name::from_string("HAdd"),
        Name::from_string("hAdd"),
        Name::from_string("Nat.add"),
        Name::from_string("a.b.c.HAdd.hAdd"),
        Name::anon().str("HAdd.hAdd"),
        Name::anon().str("HAdd").str(""),
        Name::anon().str("").str("hAdd"),
        Name::anon().str("x").num(0),
        Name::anon().str("x").num(1_234_567),
        Name::anon().num(u64::MAX),
        Name::anon().str("HShiftRight").str("hShiftRight"),
    ]
}

#[test]
fn test_name_display_eq_agrees_with_to_string_on_every_pair() {
    let names = corpus();
    let mut texts: Vec<String> = names.iter().map(Name::to_string).collect();
    texts.extend(HETERO_OP_PROJECTIONS.iter().map(|p| (*p).to_owned()));
    texts.extend(
        [
            "",
            ".",
            "HAdd.",
            ".hAdd",
            "HAdd..hAdd",
            "x.00",
            "x.0",
            "[anonymous]",
        ]
        .map(str::to_owned),
    );
    for name in &names {
        for text in &texts {
            assert_eq!(
                name_display_eq(name, text),
                name.to_string() == *text,
                "name {name:?} rendered {:?} against {text:?}",
                name.to_string()
            );
        }
    }
}

#[test]
fn test_is_hetero_op_projection_matches_the_rendered_table() {
    for name in corpus() {
        assert_eq!(
            is_hetero_op_projection(&name),
            HETERO_OP_PROJECTIONS.contains(&name.to_string().as_str()),
            "{name:?}"
        );
    }
    assert!(is_hetero_op_projection(&Name::from_string("HMul.hMul")));
    assert!(!is_hetero_op_projection(&Name::from_string("HMul.hmul")));
}

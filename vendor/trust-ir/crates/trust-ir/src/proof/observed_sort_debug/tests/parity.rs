// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_seven_ordinary_variants_have_the_exact_default_debug_spelling() {
    let expected = [
        "Bool",
        "Int",
        "BitVec(64)",
        "Array(Int, Bool)",
        "Float { eb: 8, sb: 24 }",
        "RoundingMode",
        "Datatype { name: \"D\", constructors: [] }",
    ];
    for (value, expected) in examples().iter().zip(expected) {
        assert_eq!(execute(value).0, expected);
    }
}
#[test]
fn fixed_decimal_extremes_are_spelled_without_sort_validity_checks() {
    for bits in [0, 1, 8, 64, u32::MAX] {
        assert_eq!(
            execute(&ClauseSort::BitVec(bits)).0,
            format!("BitVec({bits})")
        );
        for sb in [0, 1, u32::MAX] {
            assert_eq!(
                execute(&ClauseSort::Float { eb: bits, sb }).0,
                format!("Float {{ eb: {bits}, sb: {sb} }}")
            );
        }
    }
}
#[test]
fn array_children_keep_index_then_value_order_for_every_pair_of_current_tags() {
    for index in examples() {
        for value in examples() {
            let array = ClauseSort::Array(Box::new(index.clone()), Box::new(value));
            execute(&array);
        }
    }
}
#[test]
fn empty_named_datatype_empty_constructor_and_empty_field_names_preserve_all_brackets() {
    let value = ClauseSort::Datatype {
        name: String::new(),
        constructors: vec![
            (String::new(), Vec::new()),
            ("C".into(), vec![(String::new(), ClauseSort::Int)]),
        ],
    };
    assert_eq!(
        execute(&value).0,
        "Datatype { name: \"\", constructors: [(\"\", []), (\"C\", [(\"\", Int)])] }"
    );
}
#[test]
fn repeated_constructor_and_field_names_keep_all_physical_order_and_duplicates() {
    let value = ClauseSort::Datatype {
        name: "D".into(),
        constructors: vec![
            (
                "same".into(),
                vec![
                    ("x".into(), ClauseSort::Int),
                    ("x".into(), ClauseSort::Bool),
                ],
            ),
            ("same".into(), vec![("x".into(), ClauseSort::RoundingMode)]),
            ("last".into(), Vec::new()),
        ],
    };
    let text = execute(&value).0;
    assert_eq!(
        text,
        "Datatype { name: \"D\", constructors: [(\"same\", [(\"x\", Int), (\"x\", Bool)]), (\"same\", [(\"x\", RoundingMode)]), (\"last\", [])] }"
    );
}
#[test]
fn scalar_debug_escaping_matches_strings_in_every_owned_name_position() {
    let text =
        "'\"\\\0\n\t\r\u{7f}\u{85}\u{a0}\u{301}\u{200d}\u{fe0f}\u{e000}\u{378}\u{10ffff}λ文🦀";
    let value = ClauseSort::Datatype {
        name: text.into(),
        constructors: vec![(text.into(), vec![(text.into(), ClauseSort::Bool)])],
    };
    let rendered = execute(&value).0;
    let quoted = format!("{text:?}");
    assert_eq!(rendered.matches(quoted.as_str()).count(), 3);
    assert!(!rendered.contains("\\'"));
}
#[test]
fn multiline_utf8_tails_and_printable_scalar_boundaries_are_not_truncated() {
    for text in [
        "", "é", "文", "🦀", "a\u{301}", "\u{301}a", "\u{2028}", "\u{2029}", "\u{1f}",
    ] {
        let tail = format!("{}TAIL'\"\n", text.repeat(300));
        let value = ClauseSort::Datatype {
            name: tail.clone(),
            constructors: vec![("C".into(), vec![(tail, ClauseSort::Int)])],
        };
        execute(&value);
    }
}
#[test]
fn wide_constructor_and_field_scans_include_every_empty_and_nonempty_physical_row() {
    let value = ClauseSort::Datatype {
        name: "wide".into(),
        constructors: (0..70)
            .map(|i| {
                (
                    format!("C{i}"),
                    if i % 2 == 0 {
                        Vec::new()
                    } else {
                        (0..40)
                            .map(|j| (format!("f{j}"), ClauseSort::BitVec(j)))
                            .collect()
                    },
                )
            })
            .collect(),
    };
    let text = execute(&value).0;
    assert!(text.contains("(\"C0\", [])"));
    assert!(text.contains("(\"C69\", [(\"f0\", BitVec(0))"));
    assert!(text.ends_with("(\"f39\", BitVec(39))])] }"));
}
#[test]
fn iterative_nested_arrays_preserve_full_default_debug_expression() {
    let mut value = mixed();
    for _ in 0..120 {
        value = ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(value));
    }
    let text = execute(&value).0;
    assert_eq!(text.matches("Array(").count(), 121);
    assert!(text.ends_with(&")".repeat(120)));
}
#[test]
fn diagnostic_spelling_does_not_consume_interpreter_fuel_even_when_none_remains() {
    let value = mixed();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut observer,
    );
    assert_eq!(
        value.debug_observed(&mut session, site()).unwrap(),
        format!("{value:?}")
    );
    assert_eq!(session.remaining_fuel(), 0);
    assert!(session.first_refusal().is_none());
}

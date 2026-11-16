// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests of the strict tokenizer (`json.rs`). The reader, loader and
//! replay are tested end to end in `tests/ndjson_front_door.rs`.

use super::error::JsonError;
use super::json::{parse_line, JsonValue, MAX_DEPTH};

fn parse(s: &str) -> Result<JsonValue, JsonError> {
    parse_line(s.as_bytes())
}

#[test]
fn test_json_accepts_a_record_with_surrounding_whitespace() {
    let v = parse(" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}\r").expect("well-formed");
    let JsonValue::Object(entries) = v else {
        panic!("an object");
    };
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].0, "in");
}

#[test]
fn test_json_trailing_bytes_are_refused() {
    // lean4#15542: `{..} x` and two objects on one line.
    assert!(matches!(
        parse("{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}} x"),
        Err(JsonError::TrailingBytes { offset: 35 })
    ));
    assert!(matches!(
        parse("{\"a\":1}{\"b\":2}"),
        Err(JsonError::TrailingBytes { offset: 7 })
    ));
}

#[test]
fn test_json_duplicate_keys_are_refused_after_unescaping() {
    assert!(matches!(
        parse("{\"in\":1,\"in\":2}"),
        Err(JsonError::DuplicateKey { ref key, .. }) if key == "in"
    ));
    // `\u0070re` is `pre`: compared after unescaping (lean4#15628).
    assert!(matches!(
        parse("{\"str\":{\"pre\":0,\"\\u0070re\":1}}"),
        Err(JsonError::DuplicateKey { ref key, .. }) if key == "pre"
    ));
    // The same key in two different objects is no duplicate.
    parse("{\"a\":{\"a\":1}}").expect("distinct objects");
}

#[test]
fn test_json_exponent_cap_is_100000() {
    parse("[1e100000]").expect("at the cap");
    parse("[1E+99999]").expect("below the cap");
    assert!(matches!(
        parse("[1e100001]"),
        Err(JsonError::ExponentTooLarge { offset: 1 })
    ));
    // A run of digits saturates; it never wraps to a small exponent.
    assert!(matches!(
        parse("[1e99999999999999999999999999]"),
        Err(JsonError::ExponentTooLarge { .. })
    ));
    // Negative exponents are not capped (Lean caps only `shiftl`).
    parse("[1e-999999]").expect("negative exponent");
}

#[test]
fn test_json_leading_zeros_are_not_json() {
    assert!(matches!(
        parse("[007]"),
        Err(JsonError::UnexpectedByte { .. })
    ));
}

#[test]
fn test_json_canonical_natural_flags() {
    let JsonValue::Array(items) =
        parse("[0, 42, -0, 1.0, 1e2, 18446744073709551616]").expect("valid numbers")
    else {
        panic!("an array");
    };
    let nats: Vec<Option<u64>> = items
        .iter()
        .map(|v| match v {
            JsonValue::Number(n) => n.as_u64(),
            _ => None,
        })
        .collect();
    assert_eq!(nats, vec![Some(0), Some(42), None, None, None, None]);
}

#[test]
fn test_json_lone_surrogates_and_bad_escapes_are_refused() {
    assert_eq!(
        parse("\"\\ud83d\\ude00\"").expect("a surrogate pair"),
        JsonValue::String("\u{1F600}".to_owned())
    );
    assert!(matches!(
        parse("\"\\ud83d\""),
        Err(JsonError::InvalidEscape { .. })
    ));
    assert!(matches!(
        parse("\"\\ude00\""),
        Err(JsonError::InvalidEscape { .. })
    ));
    assert!(matches!(
        parse("\"\\x41\""),
        Err(JsonError::InvalidEscape { .. })
    ));
    assert!(matches!(
        parse("\"a\u{1}b\""),
        Err(JsonError::ControlCharacter { .. })
    ));
}

#[test]
fn test_json_nesting_is_bounded_and_iterative() {
    let deep = "[".repeat(MAX_DEPTH + 1);
    assert!(matches!(parse(&deep), Err(JsonError::TooDeep { .. })));
    let ok = format!("{}{}", "[".repeat(MAX_DEPTH), "]".repeat(MAX_DEPTH));
    parse(&ok).expect("at the bound");
}

#[test]
fn test_json_malformed_inputs_never_panic() {
    for input in [
        "",
        " ",
        "{",
        "}",
        "[",
        "{\"a\"",
        "{\"a\":",
        "{\"a\":1,",
        "[1,]",
        "[,1]",
        "-",
        "1.",
        "1e",
        "1e+",
        "tru",
        "nul",
        "\"\\u12\"",
        "{1:2}",
        "\u{0}",
        "\"\\",
    ] {
        assert!(parse(input).is_err(), "{input:?} must be refused");
    }
    assert!(matches!(
        parse_line(&[0x7b, 0xff, 0x7d]),
        Err(JsonError::InvalidUtf8 { offset: 1 })
    ));
}

#[test]
fn test_ndjson_rule_sets_name_the_r81_oracle_world() {
    // Every reviewed row judges by the kernel of R81's oracle world; the day
    // the oracle moves this fails, and the rows are reviewed again.
    for row in super::REVIEWED_LEAN_VERSIONS {
        let world = row.rule_set.world();
        let oracle = crate::world::lean_worlds()
            .iter()
            .find(|w| w.state == crate::world::WorldState::Oracle)
            .expect("lean_worlds.tsv has an oracle row");
        assert_eq!(world, oracle.world, "{}: its rule set's world", row.version);
    }
}

#[test]
fn test_lean_foundational_axioms_are_kernel_foundational() {
    for axiom in super::LEAN_FOUNDATIONAL_AXIOMS {
        assert!(
            clean_kernel::is_foundational_axiom(&clean_kernel::name::Name::from_string(axiom)),
            "`{axiom}` is permitted in an export but is not foundational in Clean's kernel"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One export line as bytes, spelled the way `Lean.Json.compress` spells it.
//!
//! lean4export builds every record as a `Lean.Json` object and prints it with
//! `compress`: no whitespace, an object's keys in code-point order (the
//! object is a red-black tree keyed by the string), and a string escaped by
//! `Lean.Json.escape` (pinned v4.30.0-rc2, `Lean/Data/Json/Printer.lean`):
//! `"` and `\` behind a backslash, `\n` and `\r` by their short forms, every
//! other character below U+0020 as `\u00XX` in lowercase hexadecimal, and
//! everything else as itself, U+007F and the astral planes included. This
//! writer sorts the keys itself rather than trusting the order a record is
//! built in, so a record cannot be written in another order.

/// A JSON value this writer writes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Json {
    /// A natural number.
    Nat(u64),
    /// A boolean.
    Bool(bool),
    /// A string, not yet escaped.
    Str(String),
    /// An array.
    Array(Vec<Json>),
    /// An object; its keys are sorted when it is rendered.
    Object(Vec<(&'static str, Json)>),
}

impl Json {
    /// An array of naturals.
    pub(super) fn nats(items: &[u64]) -> Self {
        Json::Array(items.iter().copied().map(Json::Nat).collect())
    }

    /// Append this value to `out`.
    pub(super) fn render(&self, out: &mut Vec<u8>) {
        match self {
            Json::Nat(n) => out.extend_from_slice(n.to_string().as_bytes()),
            Json::Bool(true) => out.extend_from_slice(b"true"),
            Json::Bool(false) => out.extend_from_slice(b"false"),
            Json::Str(text) => escape(text, out),
            Json::Array(items) => {
                out.push(b'[');
                for (at, item) in items.iter().enumerate() {
                    if at > 0 {
                        out.push(b',');
                    }
                    item.render(out);
                }
                out.push(b']');
            }
            Json::Object(entries) => {
                let mut sorted: Vec<&(&'static str, Json)> = entries.iter().collect();
                sorted.sort_by_key(|(key, _)| *key);
                out.push(b'{');
                for (at, (key, value)) in sorted.into_iter().enumerate() {
                    if at > 0 {
                        out.push(b',');
                    }
                    escape(key, out);
                    out.push(b':');
                    value.render(out);
                }
                out.push(b'}');
            }
        }
    }
}

/// `text` as a JSON string, escaped as `Lean.Json.escape` escapes it.
fn escape(text: &str, out: &mut Vec<u8>) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    out.push(b'"');
    for c in text.chars() {
        match c {
            '"' => out.extend_from_slice(b"\\\""),
            '\\' => out.extend_from_slice(b"\\\\"),
            '\n' => out.extend_from_slice(b"\\n"),
            '\r' => out.extend_from_slice(b"\\r"),
            c if (c as u32) < 0x20 => {
                let n = c as usize;
                out.extend_from_slice(b"\\u00");
                out.push(HEX[n / 16]);
                out.push(HEX[n % 16]);
            }
            c => {
                let mut buf = [0u8; 4];
                out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
            }
        }
    }
    out.push(b'"');
}

#[cfg(test)]
mod tests {
    use super::Json;

    fn rendered(value: &Json) -> String {
        let mut out = Vec::new();
        value.render(&mut out);
        String::from_utf8(out).expect("the writer writes UTF-8")
    }

    #[test]
    fn test_json_object_keys_are_written_in_code_point_order() {
        let value = Json::Object(vec![
            ("type", Json::Nat(3)),
            ("isUnsafe", Json::Bool(false)),
            ("isRec", Json::Bool(true)),
            ("isReflexive", Json::Bool(false)),
            ("all", Json::nats(&[1, 2])),
        ]);
        assert_eq!(
            rendered(&value),
            r#"{"all":[1,2],"isRec":true,"isReflexive":false,"isUnsafe":false,"type":3}"#
        );
    }

    #[test]
    fn test_json_strings_are_escaped_as_lean_escapes_them() {
        let value = Json::Str("a\"b\\c\nd\re\tf\u{0}g\u{7f}h\u{1F600}α".to_owned());
        assert_eq!(
            rendered(&value),
            "\"a\\\"b\\\\c\\nd\\re\\u0009f\\u0000g\u{7f}h\u{1F600}α\""
        );
    }

    #[test]
    fn test_json_escaped_strings_read_back_through_the_strict_tokenizer() {
        use crate::ndjson::json::{parse_line, JsonValue};
        for text in [
            "",
            "plain",
            "a\"b\\c\nd\re\tf\u{0}g\u{7f}h\u{1F600}α",
            "\u{1f}",
        ] {
            let mut line = Vec::new();
            Json::Array(vec![Json::Str(text.to_owned())]).render(&mut line);
            let JsonValue::Array(items) = parse_line(&line).expect("well-formed") else {
                panic!("an array");
            };
            assert!(
                matches!(&items[0], JsonValue::String(s) if s == text),
                "{text:?}"
            );
        }
    }
}

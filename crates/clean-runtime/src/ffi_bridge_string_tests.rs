// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! String operations of the FFI native function bridge.

use super::*;

// ---------------------------------------------------------------------------
// String operations
// ---------------------------------------------------------------------------

#[test]
fn test_string_append_basic() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native(
            "String.append",
            &[
                Value::String("hello".into()),
                Value::String(" world".into()),
            ],
        )
        .expect("append should succeed");
    assert_eq!(result, Value::String("hello world".into()));
}

#[test]
fn test_string_length_counts_unicode_code_points() {
    let bridge = FfiBridge::new();
    // Exact lengths from the retained official 4.30.0-rc2 and 4.35.0 source
    // fixture. Combining marks are separate code points, and U+0000 counts.
    for (text, expected) in [
        ("", 0),
        ("ascii", 5),
        ("é€😀", 3),
        ("\0é€😀", 4),
        ("e\u{301}", 2),
    ] {
        let result = bridge
            .call_native("String.length", &[Value::String(text.into())])
            .expect("length should succeed");
        assert_eq!(result, Value::Nat(expected), "{text:?}");
    }
}

#[test]
fn test_string_push_appends_char() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native(
            "String.push",
            &[Value::String("hell".into()), Value::Nat(97)], // 'a'
        )
        .expect("push should succeed");
    assert_eq!(result, Value::String("hella".into()));
}

#[test]
fn test_string_mk_from_char_codes() {
    let bridge = FfiBridge::new();
    let codes = Value::Array(vec![Value::Nat(104), Value::Nat(105)]); // 'h', 'i'
    let result = bridge
        .call_native("String.mk", &[codes])
        .expect("mk should succeed");
    assert_eq!(result, Value::String("hi".into()));
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Debug-info source-file table round-trip: `SourceSpan::file` indexes
// `Module::files`. Closes the audit fitness-gap "debug info is structurally
// present but unusable — SourceSpan.file has no file table". These tests use
// the core crate directly (no builder) so they exercise the binary + text
// codecs under trust-ir's own `binary`/`parser` features.

use trust_ir::Module;

#[test]
fn intern_file_is_idempotent_and_indexed() {
    let mut m = Module::new("dbg");
    assert_eq!(m.intern_file("src/main.rs"), 0);
    assert_eq!(m.intern_file("src/lib.rs"), 1);
    assert_eq!(m.intern_file("src/main.rs"), 0, "idempotent");
    assert_eq!(m.files.len(), 2);
    assert_eq!(m.file_name(0), Some("src/main.rs"));
    assert_eq!(m.file_name(2), None);
}

#[cfg(feature = "binary")]
#[test]
fn file_table_binary_round_trip() {
    let mut m = Module::new("dbg");
    m.intern_file("a/b/c.rs");
    m.intern_file("d/e.rs");
    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("binary round trip");
    assert_eq!(back.files, m.files);
}

#[cfg(feature = "binary")]
#[test]
fn empty_file_table_binary_round_trip() {
    let m = Module::new("dbg");
    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("round trip");
    assert!(back.files.is_empty());
}

#[cfg(feature = "parser")]
#[test]
fn file_table_text_round_trip() {
    let mut m = Module::new("dbg");
    m.intern_file("a/b/c.rs");
    m.intern_file("d/e.rs");
    let text = format!("{m}");
    assert!(text.contains("file 0 \"a/b/c.rs\""), "text: {text}");
    assert!(text.contains("file 1 \"d/e.rs\""), "text: {text}");
    let reparsed = trust_ir::parser::parse_module(&text).expect("text round trip");
    assert_eq!(reparsed.files, m.files);
}

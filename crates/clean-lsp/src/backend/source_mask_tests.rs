// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the code/comment/string classification.

use super::SourceMask;

/// Every byte offset at which `needle` occurs, and whether the mask calls that
/// span code. Written this way because every test below asks the same
/// question: "is the occurrence in THIS position a reference?"
fn occurrences(text: &str, needle: &str) -> Vec<bool> {
    let mask = SourceMask::new(text);
    let mut out = Vec::new();
    let mut from = 0usize;
    while let Some(rel) = text[from..].find(needle) {
        let at = from + rel;
        out.push(mask.span_is_code(at, at + needle.len()));
        from = at + 1;
    }
    out
}

#[test]
fn test_source_mask_plain_code_is_all_code() {
    assert_eq!(
        occurrences("def myLemma := myLemma", "myLemma"),
        [true, true]
    );
}

#[test]
fn test_source_mask_line_comment_is_not_code() {
    let text = "def myLemma := 1\n-- myLemma is the interesting one\ndef b := myLemma\n";
    assert_eq!(occurrences(text, "myLemma"), [true, false, true]);
}

#[test]
fn test_source_mask_line_comment_ends_at_the_newline() {
    // The occurrence on the NEXT line is code again. A mask that ran a line
    // comment to end-of-file would silently drop every later reference, which
    // fails safe for rename but makes find-references wrong.
    assert_eq!(
        occurrences("-- myLemma\nmyLemma\n", "myLemma"),
        [false, true]
    );
}

#[test]
fn test_source_mask_block_comment_is_not_code() {
    assert_eq!(
        occurrences("/- myLemma -/ myLemma", "myLemma"),
        [false, true]
    );
}

#[test]
fn test_source_mask_block_comments_nest() {
    // THE ONE THING A NAIVE SCANNER GETS WRONG. Looking for the first `-/`
    // would end the comment at the inner close, so the trailing `myLemma`
    // inside the outer comment would be reported as a reference — and renamed.
    let text = "/- a /- b -/ myLemma -/ myLemma";
    assert_eq!(occurrences(text, "myLemma"), [false, true]);
}

#[test]
fn test_source_mask_doc_comment_forms_need_no_special_case() {
    for open in ["/--", "/-!"] {
        let text = format!("{open} myLemma -/\nmyLemma");
        assert_eq!(
            occurrences(&text, "myLemma"),
            [false, true],
            "{open} is a block comment and must mask like one"
        );
    }
}

#[test]
fn test_source_mask_string_literal_is_not_code() {
    assert_eq!(
        occurrences("def s := \"myLemma\"\ndef b := myLemma", "myLemma"),
        [false, true]
    );
}

#[test]
fn test_source_mask_escaped_quote_does_not_close_the_string() {
    // `"a\"myLemma"` is ONE string. A scanner that closed at the escaped quote
    // would call the rest of the string code and rename inside it.
    assert_eq!(
        occurrences("def s := \"a\\\"myLemma\"\nmyLemma", "myLemma"),
        [false, true]
    );
}

#[test]
fn test_source_mask_comment_markers_inside_a_string_are_not_comments() {
    assert_eq!(
        occurrences("def s := \"-- /- \"\nmyLemma", "myLemma"),
        [true],
        "a `--` inside a string must not open a comment and swallow the file"
    );
}

#[test]
fn test_source_mask_quote_inside_a_comment_does_not_open_a_string() {
    assert_eq!(
        occurrences("-- he said \"hi\nmyLemma", "myLemma"),
        [true],
        "an unbalanced quote in a comment must not turn the rest of the file into a string"
    );
}

#[test]
fn test_source_mask_unterminated_regions_stay_masked() {
    // Conservative on purpose: an occurrence not returned is a reference the
    // user does not see, while one wrongly returned is a rename that edits
    // their comment.
    assert_eq!(occurrences("/- myLemma", "myLemma"), [false]);
    assert_eq!(occurrences("def s := \"myLemma", "myLemma"), [false]);
}

#[test]
fn test_source_mask_is_utf8_safe() {
    // Non-ASCII before and inside the masked regions. Byte scanning is correct
    // because every delimiter is ASCII and a continuation byte is >= 0x80, but
    // that is worth a test rather than a comment.
    let text = "def λx := myLemma\n-- ∀ myLemma ∎\ndef π := myLemma";
    assert_eq!(occurrences(text, "myLemma"), [true, false, true]);
}

#[test]
fn char_literal_is_excluded_by_the_identifier_boundary_not_by_this_mask() {
    // Character literals are deliberately NOT masked: `'` is an identifier
    // CONTINUE character here, so treating it as a delimiter would read `h'`
    // as opening a literal and swallow the rest of the file. It costs nothing,
    // and this is the measurement of that claim — the mask calls `'a'` code,
    // and the identifier-boundary check is what rejects it.
    assert_eq!(occurrences("def c := 'a'", "a"), [true]);

    let text = "def c := 'a'";
    let at = text.find("'a'").expect("the literal") + 1;
    assert!(
        crate::backend::CleanBackend::is_identifier_continue('\''),
        "if ' ever stops being identifier-continue, char literals need real masking"
    );
    let before = text[..at].chars().next_back().expect("a preceding char");
    let after = text[at + 1..].chars().next().expect("a following char");
    assert!(
        crate::backend::CleanBackend::is_identifier_continue(before)
            && crate::backend::CleanBackend::is_identifier_continue(after),
        "the char literal's payload is bounded by ' on both sides, which is what rejects it"
    );
}

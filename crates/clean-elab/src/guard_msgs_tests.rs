// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit pins for `#guard_msgs`'s comparison (`Lean/Elab/GuardMsgs.lean`).
//! The command end to end is pinned in `tests/guard_commands_e2e.rs`.

use super::*;

fn info(text: &str) -> CommandMessage {
    CommandMessage::info(text)
}

fn error(text: &str) -> CommandMessage {
    CommandMessage {
        severity: MessageSeverity::Error,
        text: text.to_owned(),
    }
}

fn matched(doc: Option<&str>, spec: &[GuardMsgsSpecElt], messages: &[CommandMessage]) -> bool {
    matches!(judge(doc, spec, messages), GuardMsgsVerdict::Matched(_))
}

#[test]
fn test_judge_no_doc_and_no_messages_matches() {
    assert!(matched(None, &[], &[]));
    assert!(!matched(None, &[], &[info("x")]));
}

#[test]
fn test_judge_doc_is_trimmed_and_marker_removed() {
    // `⏎` protects trailing whitespace in a docstring; it is removed before
    // comparing, and exact mode then sees the protected space.
    let exact = [GuardMsgsSpecElt::Whitespace(GuardMsgsWhitespace::Exact)];
    assert!(matched(
        Some("\n info: a ⏎\nb \n"),
        &exact,
        &[info("a \nb")]
    ));
    assert!(!matched(Some("info: a\nb"), &exact, &[info("a \nb")]));
}

#[test]
fn test_judge_messages_are_joined_with_separator() {
    let doc = "info: one\n---\nerror: two";
    assert!(matched(Some(doc), &[], &[info("one"), error("two")]));
    assert!(!matched(Some(doc), &[], &[error("two"), info("one")]));
    let sorted = [GuardMsgsSpecElt::Ordering(GuardMsgsOrdering::Sorted)];
    assert!(matched(
        Some("error: two\n---\ninfo: one"),
        &sorted,
        &[info("one"), error("two")]
    ));
}

#[test]
fn test_judge_leftmost_filter_decides() {
    let error_then_drop_all = [
        GuardMsgsSpecElt::Filter {
            drop: false,
            severity: GuardMsgsSeverity::Error,
        },
        GuardMsgsSpecElt::Filter {
            drop: true,
            severity: GuardMsgsSeverity::All,
        },
    ];
    assert!(matched(
        Some("error: e"),
        &error_then_drop_all,
        &[info("i"), error("e")]
    ));
    // A severity no clause names passes through, unchecked.
    let info_only = [GuardMsgsSpecElt::Filter {
        drop: false,
        severity: GuardMsgsSeverity::Info,
    }];
    match judge(Some("info: i"), &info_only, &[info("i"), error("e")]) {
        GuardMsgsVerdict::Matched(passthrough) => assert_eq!(passthrough, vec![error("e")]),
        GuardMsgsVerdict::Mismatch(m) => panic!("{m}"),
    }
}

#[test]
fn test_judge_first_written_whitespace_clause_wins() {
    let lax_then_exact = [
        GuardMsgsSpecElt::Whitespace(GuardMsgsWhitespace::Lax),
        GuardMsgsSpecElt::Whitespace(GuardMsgsWhitespace::Exact),
    ];
    assert!(matched(
        Some("info:  a   b"),
        &lax_then_exact,
        &[info("a b")]
    ));
}

#[test]
fn test_judge_mismatch_reports_lean_message() {
    match judge(Some("info: x"), &[], &[info("y")]) {
        GuardMsgsVerdict::Mismatch(m) => assert_eq!(
            m,
            "❌ Docstring on `#guard_msgs` does not match generated message:\n\ninfo: y"
        ),
        GuardMsgsVerdict::Matched(_) => panic!("must not match"),
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp: no progress made` prints the goal it gave up on.
//!
//! The 2026-08-25 source-elab corpus recorded 16 `simp: no progress made` and 11
//! `grind: no progress made` entries in which the message was the ENTIRE record —
//! no goal, no target, nothing to classify. 38 of that report's 74 `tactic
//! failed` rows carried no payload for the same reason, and no regrouping of the
//! committed text recovers information that was never printed
//! (`docs/analysis/srcelab-bucket-decomposition-2026-08-28.md` §3.1, §6). The
//! limit was the emitter, so the emitter is what changed.
//!
//! These tests drive the production path — `parse_file` → preprocess →
//! elaborate — and read the rendered `Display` string, because that string is
//! the artifact a corpus run records. Asserting on the `goal` FIELD instead
//! would pass even if the format attribute dropped it.
//!
//! The negative half matters as much as the positive one: the same variant is
//! used as internal control flow by every closer wrapped in
//! `try_tactic_preserving_state`, and those must keep costing nothing and
//! rendering the bare message.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::tactic::TacticError;
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};

/// Elaborate `code` against one fresh prelude env and return the LAST result.
fn elab_last(code: &str) -> Result<crate::ElabResult, ElabError> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    let mut last = None;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = Some(elaborate_decl_and_register_with_context(
            &mut env,
            &processed,
            &mut file_ctx,
        ));
    }
    last.expect("at least one declaration")
}

/// The rendered error of a declaration expected to fail, or a panic naming what
/// happened instead.
#[track_caller]
fn failure_text(code: &str, what: &str) -> String {
    match elab_last(code) {
        Err(err) => err.to_string(),
        Ok(ok) => panic!("{what}: expected a failure, got {ok:?}"),
    }
}

/// A goal no `@[simp]` lemma touches and no simp closer closes: two distinct
/// opaque propositions, with the hypothesis deliberately unrelated to the
/// target so `assumption` cannot fire either.
const NO_PROGRESS_SNIPPET: &str = r"
axiom P : Prop
axiom Q : Prop
theorem t (h : P) : Q := by simp
";

#[test]
fn test_simp_no_progress_message_names_the_tactic() {
    let text = failure_text(NO_PROGRESS_SNIPPET, "simp on an untouchable goal");
    assert!(
        text.contains("simp: no progress made"),
        "the historical message must survive verbatim as the prefix, got: {text}"
    );
}

#[test]
fn test_simp_no_progress_message_prints_the_goal() {
    let text = failure_text(NO_PROGRESS_SNIPPET, "simp on an untouchable goal");
    assert!(
        text.contains('\u{22a2}'),
        "the message must carry a turnstile line — this is the whole point of \
         the change; without it a corpus entry is unclassifiable. Got: {text}"
    );
    assert!(
        text.contains('Q'),
        "the message must name the target it gave up on, got: {text}"
    );
}

#[test]
fn test_simp_no_progress_message_prints_the_hypotheses() {
    let text = failure_text(NO_PROGRESS_SNIPPET, "simp on an untouchable goal");
    let goal_block = text
        .split_once("no progress made")
        .expect("the message shape is asserted by the sibling test")
        .1;
    assert!(
        goal_block.contains("h :"),
        "the local context belongs in the goal block: a `no progress` a reader \
         cannot reproduce is what this replaced. Got: {text}"
    );
}

/// The bare message is still exactly the old string when no goal is attached.
/// Every internal closer takes this path, and several dozen call sites across
/// the tactic tree rely on it.
#[test]
fn test_no_progress_without_a_goal_renders_the_bare_message() {
    let err = TacticError::no_progress("simp");
    assert_eq!(
        err.to_string(),
        "simp: no progress made",
        "the goal-less rendering must not gain a suffix"
    );
}

/// An empty goal string is treated as no goal, so a degenerate render cannot
/// leave a dangling `on` with nothing after it.
#[test]
fn test_no_progress_with_an_empty_goal_renders_the_bare_message() {
    let err = TacticError::no_progress_on("simp", "");
    assert_eq!(err.to_string(), "simp: no progress made");
}

/// The constructor that carries a goal renders it, and keeps the old prefix.
#[test]
fn test_no_progress_on_renders_prefix_then_goal() {
    let err = TacticError::no_progress_on("simp", "h : P\n\u{22a2} Q");
    let text = err.to_string();
    assert!(
        text.starts_with("simp: no progress made"),
        "prefix must be unchanged, got: {text}"
    );
    assert!(
        text.contains("\u{22a2} Q"),
        "goal must be rendered, got: {text}"
    );
}

/// `simp at h` is a distinct emitter site and was equally silent.
#[test]
fn test_simp_at_hypothesis_no_progress_prints_the_goal() {
    let text = failure_text(
        r"
axiom P : Prop
axiom Q : Prop
theorem t (h : P) : Q := by simp at h
",
        "simp at an untouchable hypothesis",
    );
    assert!(
        text.contains("no progress made"),
        "expected a no-progress refusal, got: {text}"
    );
    assert!(
        text.contains('\u{22a2}'),
        "`simp at h` must print the goal too, got: {text}"
    );
}

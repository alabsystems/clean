// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `grind: no progress made` prints the goal it gave up on.
//!
//! The sibling half of `simp_no_progress_goal`. The 2026-08-25 source-elab
//! corpus recorded 11 `grind: no progress made` entries — spanning Logic/Basic
//! 3, Function/Basic 2, Data/Subtype 5, Order/Basic 1 — in which that string was
//! the ENTIRE record. Together with `simp`'s 16 they are the 27-entry
//! information hole of
//! `docs/analysis/srcelab-bucket-decomposition-2026-08-28.md` §3.1: nothing was
//! truncated, nothing was ever printed, and no regrouping of committed text
//! recovers them.
//!
//! `grind` has four escaping exits, all in `grind_core` — the bare
//! no-progress, the split-branch no-progress, `grind/max-depth` and
//! `grind/split-limit` — and three swallowed ones: `try_propext_bridge` and
//! `try_funext_propext_bridge` (called as `let _ = …`) and the automation
//! engine inside `try_tactic_preserving_state`. Only the escaping four carry a
//! goal; the swallowed three must stay free, which `grind_tests`'
//! `test_grind_resource_limit_diagnostics_are_stable` pins from the other side.
//!
//! After a case split the reported goal is the BRANCH grind died on rather than
//! the goal the user wrote. That is what the message says, it is the more useful
//! of the two, and `grind_with_config`'s own contract ("state may be partially
//! modified even on failure") means no site could report the original anyway.

use clean_kernel::Environment;
use clean_parser::parse_file;

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

#[track_caller]
fn failure_text(code: &str, what: &str) -> String {
    match elab_last(code) {
        Err(err) => err.to_string(),
        Ok(ok) => panic!("{what}: expected a failure, got {ok:?}"),
    }
}

/// Two unrelated opaque propositions: no closer fires, no congruence closure
/// path exists, and there is nothing to split on, so `grind_core` reaches its
/// bare `GRIND_NO_PROGRESS` exit.
const NO_PROGRESS_SNIPPET: &str = r"
axiom P : Prop
axiom Q : Prop
theorem t (h : P) (n : Nat) : Q := by grind
";

#[test]
fn test_grind_no_progress_message_names_the_tactic() {
    let text = failure_text(NO_PROGRESS_SNIPPET, "grind on an unreachable goal");
    assert!(
        text.contains("grind: no progress made"),
        "the historical message must survive verbatim as the prefix, got: {text}"
    );
}

#[test]
fn test_grind_no_progress_message_prints_the_goal() {
    let text = failure_text(NO_PROGRESS_SNIPPET, "grind on an unreachable goal");
    assert!(
        text.contains('\u{22a2}'),
        "the message must carry a turnstile line — without it the entry is \
         unclassifiable, which is the defect this replaced. Got: {text}"
    );
    assert!(
        text.contains('Q'),
        "the message must name the target it gave up on, got: {text}"
    );
}

#[test]
fn test_grind_no_progress_message_prints_the_hypotheses() {
    let text = failure_text(NO_PROGRESS_SNIPPET, "grind on an unreachable goal");
    let goal_block = text
        .split_once("no progress made")
        .expect("the message shape is asserted by the sibling test")
        .1;
    assert!(
        goal_block.contains("h :"),
        "the local context belongs in the goal block, got: {text}"
    );
    assert!(
        goal_block.contains("n :"),
        "every hypothesis, not just the first, got: {text}"
    );
}

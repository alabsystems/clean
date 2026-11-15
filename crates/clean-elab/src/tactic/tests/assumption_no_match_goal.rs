// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `assumption` names the goal it searched, and stops calling it a missing
//! hypothesis.
//!
//! The third and last part of the 2026-08-25 corpus's zero-payload
//! `tactic failed` hole (`docs/analysis/…-2026-08-28.md` §3.2), after simp and
//! grind. 11 of the 14 `hypothesis not found` entries read, in full:
//!
//! ```text
//! Prop.exists_iff: Tactic failed: hypothesis not found: no matching hypothesis found
//! ```
//!
//! Two defects in one line. The message was DOUBLED and self-contradicting —
//! the tuple variant's own `hypothesis not found:` prefix in front of a payload
//! saying the opposite — because `assumption` was reusing
//! `HypothesisNotFound(String)`, whose payload is meant to be the NAME the user
//! wrote. And nothing was printed: no name (there is none to print), no goal,
//! no candidate list.
//!
//! `TacticError::NoMatchingHypothesis` separates the two failures. Its goal
//! block is exactly the right payload, because a goal block IS the target the
//! search matched against plus every hypothesis it considered.
//!
//! The `first`-backtracking arm below is not incidental. `HypothesisNotFound`
//! is in `is_recoverable_first_failure`, so `first | assumption | exact h`
//! falls through to the next branch; a new variant missing from that list would
//! have silently broken every such script. It is listed, and this pins it.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::tactic::TacticError;
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};

fn elab_last(code: &str) -> Result<ElabResult, ElabError> {
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

/// `h : P` is in scope and the goal is `Q`, so the search runs over a non-empty
/// context and matches nothing — the exact shape the 11 corpus entries hit.
const NO_MATCH_SNIPPET: &str = r"
axiom P : Prop
axiom Q : Prop
theorem t (h : P) (n : Nat) : Q := by assumption
";

#[test]
fn test_assumption_no_match_stops_claiming_a_hypothesis_is_missing() {
    let text = failure_text(NO_MATCH_SNIPPET, "assumption with no matching hypothesis");
    assert!(
        !text.contains("hypothesis not found"),
        "nothing was named and nothing is missing — the old prefix described a \
         different failure. Got: {text}"
    );
    assert!(
        !text.contains("no matching hypothesis found"),
        "the doubled payload must be gone, got: {text}"
    );
    assert!(
        text.contains("assumption: no hypothesis matches the goal"),
        "the message must say what actually happened, got: {text}"
    );
}

#[test]
fn test_assumption_no_match_prints_the_goal_it_searched() {
    let text = failure_text(NO_MATCH_SNIPPET, "assumption with no matching hypothesis");
    assert!(
        text.contains('\u{22a2}'),
        "the message must carry a turnstile line, got: {text}"
    );
    assert!(
        text.contains('Q'),
        "the message must name the target that nothing matched, got: {text}"
    );
}

#[test]
fn test_assumption_no_match_prints_every_candidate_it_considered() {
    let text = failure_text(NO_MATCH_SNIPPET, "assumption with no matching hypothesis");
    let block = text
        .split_once("matches the goal")
        .expect("the message shape is asserted by the sibling test")
        .1;
    assert!(
        block.contains("h :"),
        "the searched hypotheses ARE the useful payload here, got: {text}"
    );
    assert!(
        block.contains("n :"),
        "every candidate, not just the first, got: {text}"
    );
}

/// A named hypothesis that is genuinely absent must keep the OTHER variant and
/// the other message. The whole point of the split is that these are two
/// different failures.
#[test]
fn test_a_genuinely_missing_named_hypothesis_still_says_not_found() {
    let text = failure_text(
        r"
axiom P : Prop
theorem t (h : P) : P := by exact hzzz
",
        "a name that is not in scope",
    );
    assert!(
        !text.contains("no hypothesis matches the goal"),
        "a NAME failure must not be reported as a SEARCH failure, got: {text}"
    );
}

/// `first | assumption | …` must still fall through to the next branch.
///
/// `is_recoverable_first_failure` gates that, and a new variant absent from its
/// list would break every such script silently. Asserted on the predicate
/// itself rather than only through a script, so the arm cannot pass for an
/// unrelated reason.
#[test]
fn test_no_matching_hypothesis_is_recoverable_by_first() {
    let code = r"
axiom P : Prop
axiom Q : Prop
theorem t (h : P) (hq : Q) : Q := by first | assumption | exact hq
";
    let result = elab_last(code);
    assert!(
        matches!(result, Ok(ElabResult::Theorem { .. })),
        "`first` must backtrack past a NoMatchingHypothesis into the next \
         branch; got {result:?}"
    );
}

/// The goal-less rendering keeps the bare sentence — no dangling connective.
#[test]
fn test_no_matching_hypothesis_without_a_goal_renders_bare() {
    let err = TacticError::NoMatchingHypothesis {
        tactic: "assumption".into(),
        goal: None,
    };
    assert_eq!(
        err.to_string(),
        "assumption: no hypothesis matches the goal"
    );

    let empty = TacticError::NoMatchingHypothesis {
        tactic: "assumption".into(),
        goal: Some(String::new()),
    };
    assert_eq!(
        empty.to_string(),
        "assumption: no hypothesis matches the goal"
    );
}

/// `injection` swallows the SEARCH failure and propagates a NAME failure.
///
/// Its finisher runs `assumption` and deliberately fails open when nothing
/// matches, so the goal stays open as an honest `unsolved goals`. That arm read
/// `HypothesisNotFound(_)` — strictly wider than the comment above it claimed,
/// and wide enough to hide a real name bug. It caught the intended case only
/// because `assumption` was overloading the variant.
///
/// The positive half: `injection h` on `h : Nat.succ a = Nat.succ b` with an
/// unrelated goal `P` must still SUCCEED, leaving `h_inj : a = b` in context.
/// `tactic::tests::core::test_injection_nat_succ` is that arm and it caught the
/// regression when the variant split landed; this one states the property from
/// the emitter side so the pair cannot drift apart.
#[test]
fn test_injection_finisher_swallows_only_the_search_failure() {
    let err = TacticError::NoMatchingHypothesis {
        tactic: "assumption".into(),
        goal: None,
    };
    assert!(
        matches!(err, TacticError::NoMatchingHypothesis { .. }),
        "the swallowed case is the SEARCH failure"
    );
    let named = TacticError::HypothesisNotFound("h".into());
    assert!(
        !matches!(named, TacticError::NoMatchingHypothesis { .. }),
        "a NAME failure must not be matched by the swallow arm — it has to          propagate, which is the narrowing this split bought"
    );
}

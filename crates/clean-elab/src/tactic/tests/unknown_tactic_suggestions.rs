// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An unknown tactic names the tactics you might have meant — or says nothing.
//!
//! The 2026-08-25 source-elab corpus carried `unknown tactic 'inhabit'` as the
//! entire message. Both halves of a "did you mean" were already in the tree and
//! neither was wired: `TacticRegistry::names()` holds every registered name, and
//! `agent_diagnostics::nearest_string_candidates` is an edit-distance suggester
//! with its own tests. The registry is in scope at every site that minted the
//! bare error.
//!
//! The negative half is the part worth defending. A suggestion a reader must
//! evaluate and reject costs attention AND implies the real name was looked
//! for, so `TacticError::UnknownTactic` is kept for the no-near-miss case
//! rather than always emitting the three closest strings.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};

fn failure_text(code: &str) -> String {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    let mut last: Option<Result<crate::ElabResult, ElabError>> = None;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = Some(elaborate_decl_and_register_with_context(
            &mut env,
            &processed,
            &mut file_ctx,
        ));
    }
    match last.expect("at least one declaration") {
        Err(err) => err.to_string(),
        Ok(ok) => panic!("expected a failure, got {ok:?}"),
    }
}

/// A one-character typo on a real tactic is named.
#[test]
fn test_a_mistyped_tactic_suggests_the_real_one() {
    let text = failure_text(
        r"
axiom P : Prop
theorem t (h : P) : P := by exct h
",
    );
    assert!(
        text.contains("unknown tactic 'exct'"),
        "the typed name must still be quoted, got: {text}"
    );
    assert!(
        text.contains("did you mean"),
        "a one-edit typo must produce a suggestion, got: {text}"
    );
    assert!(
        text.contains("exact"),
        "and the suggestion must include the tactic actually meant, got: {text}"
    );
}

/// A name with no near miss gets NO suggestion.
///
/// This is the half that keeps the feature honest. Before the distance cutoff
/// was tightened, `inhabit` — a real Lean tactic Clean does not implement, and
/// the exact corpus face — was answered with `linarith`, which shares almost
/// nothing with it. Noise dressed as help is worse than silence.
#[test]
fn test_a_name_with_no_near_miss_suggests_nothing() {
    let text = failure_text(
        r"
axiom P : Prop
theorem t (h : P) : P := by zzzzqqqq
",
    );
    assert!(text.contains("unknown tactic 'zzzzqqqq'"), "got: {text}");
    assert!(
        !text.contains("did you mean"),
        "nothing is close to this; suggesting anything would be noise: {text}"
    );
}

/// The corpus's own face was `unknown tactic 'inhabit'`; `inhabit` is now a
/// registered tactic (`tactic/inhabit.rs`, 2026-09-12), so the same script
/// fails on inhabit's OWN terms — there is no `Nonempty P` to build an
/// `Inhabited P` from, which the pinned lean refuses too — and still carries
/// no invented suggestion.
#[test]
fn test_inhabit_is_registered_and_fails_on_its_own_terms() {
    let text = failure_text(
        r"
axiom P : Prop
theorem t (h : P) : P := by inhabit P
",
    );
    assert!(
        !text.contains("unknown tactic"),
        "`inhabit` is registered now: {text}"
    );
    assert!(text.contains("Nonempty"), "got: {text}");
    assert!(
        !text.contains("linarith"),
        "`linarith` was the measured false suggestion this cutoff removed: {text}"
    );
}

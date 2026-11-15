// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `simp` lemma-list element is Lean's `simpArg`, not a bare name.
//!
//! Lean's grammar is `simpLemma := (simpPre <|> simpPost)? "← "? term` and
//! `simpErase := "-" ident`, and `elabSimpArg` takes the by-name path only for
//! an element that resolves as an identifier; everything else is elaborated as
//! a TERM and turned into a simp theorem by `mkSimpTheoremFromExpr (inv :=
//! inv)`.
//!
//! Clean reduced every element to a `SurfaceName`, which lost three different
//! things and each face is pinned below:
//!
//! * an APPLIED argument (`@xor_not_right a`, `dif_pos h`) was refused loud —
//!   "resolve_ident: expected a name, got an application";
//! * a dotted name on a LOCAL (`h.symm`) minted the global name `h.symm`,
//!   which resolves to nothing and was dropped with NO diagnostic;
//! * the parser ate `←` and `-`, so `simp [← h]` rewrote FORWARD and
//!   `simp [-h]` ADDED the lemma Lean removes — a silent inversion of the
//!   request, measured against pinned v4.30.0-rc2, which rejects the goal
//!   Clean closed.
//!
//! Every test drives the production path (`parse_file` → preprocess →
//! elaborate → kernel), because the defect lived in the seam between the
//! parser and the simp engine.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

fn elab_all(code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

#[track_caller]
fn assert_last_closed(code: &str, what: &str) {
    let results = elab_all(code);
    let last = results.last().expect("nothing parsed");
    assert!(
        matches!(last, Ok(ElabResult::Theorem { .. })),
        "{what}: expected a kernel-registered theorem, got {last:?}"
    );
}

#[track_caller]
fn assert_last_failed(code: &str, what: &str) {
    let results = elab_all(code);
    let last = results.last().expect("nothing parsed");
    assert!(
        last.is_err(),
        "{what}: expected the declaration to be refused, got {last:?}"
    );
}

/// The shared prelude-only fixture: two opaque propositions, a proof of the
/// second, and an equation between them stated UNDER a binder so that naming
/// it needs an application.
const FIXTURE: &str = "\
axiom A : Prop
axiom B : Prop
axiom hb : B
axiom ruleAt : Nat → A = B
axiom n0 : Nat
";

// ---------------------------------------------------------------------------
// An APPLIED argument (the loud face)
// ---------------------------------------------------------------------------

/// Negative control: without the rule, the goal does not close — so every
/// pass below is attributable to the argument reaching the simp set.
#[test]
fn test_simp_only_empty_list_cannot_close_the_fixture_goal() {
    assert_last_failed(
        &format!("{FIXTURE}theorem ctl : A := by\n  simp only []\n  exact hb\n"),
        "control",
    );
}

/// `simp only [ruleAt n0]` — an application, which used to raise
/// `resolve_ident: expected a name, got an application`.
#[test]
fn test_simp_only_application_argument_is_elaborated_as_a_term() {
    assert_last_closed(
        &format!("{FIXTURE}theorem t : A := by\n  simp only [ruleAt n0]\n  exact hb\n"),
        "applied simp argument",
    );
}

/// The same through `simp` (no `only`) and through `simpa`, the other two
/// entry points that shared `simp_names`.
#[test]
fn test_simp_and_simpa_accept_an_application_argument() {
    assert_last_closed(
        &format!("{FIXTURE}theorem t : A := by\n  simp [ruleAt n0]\n  exact hb\n"),
        "applied argument under plain simp",
    );
    assert_last_closed(
        &format!("{FIXTURE}theorem t : A := by\n  simpa [ruleAt n0] using hb\n"),
        "applied argument under simpa",
    );
}

/// An `@`-explicit application — `SurfaceExpr::App(Explicit(..), _)`, the
/// shape five of the eight reported Mathlib rows carry.
#[test]
fn test_simp_only_explicit_application_argument_is_elaborated_as_a_term() {
    assert_last_closed(
        &format!("{FIXTURE}theorem t : A := by\n  simp only [@ruleAt n0]\n  exact hb\n"),
        "@-explicit applied simp argument",
    );
}

// ---------------------------------------------------------------------------
// Field notation on a LOCAL (the silent face)
// ---------------------------------------------------------------------------

/// `simp only [h.symm]` with `h` a local. `surface_expr_to_name` happily
/// minted the global name `h.symm`, `collect_extra_lemmas` found no such
/// constant and skipped it with no diagnostic, and simp reported "no progress"
/// — while `rw [h.symm]` on the same local worked (closed class 36).
#[test]
fn test_simp_only_dotted_name_on_a_local_takes_the_term_path() {
    assert_last_closed(
        // simp rewrites the goal to `B` and leaves it: Lean's simp has no
        // `assumption` step (G49), so `hb` closes it explicitly, as pinned
        // Lean 4.8.0 requires.
        "axiom A : Prop\naxiom B : Prop\n\
         theorem t (hb : B) (h : B = A) : A := by simp only [h.symm]; exact hb\n",
        "dotted name on a local",
    );
}

// ---------------------------------------------------------------------------
// The `←` modifier
// ---------------------------------------------------------------------------

/// Negative control for the `←` test: the rule FORWARD does not apply to this
/// goal, so a pass can only come from the reversed orientation.
#[test]
fn test_forward_orientation_does_not_close_the_reversed_goal() {
    assert_last_failed(
        "axiom A : Prop\naxiom B : Prop\n\
         theorem ctl (hb : B) (rule : B = A) : A := by simp only [rule]\n",
        "forward control",
    );
}

/// `simp only [← rule]` must rewrite RIGHT-to-left. The parser used to eat the
/// `←` and hand simp the forward rule (measured with
/// `CLEAN_SIMP_REWRITE_TRACE=1`: `from=R … to=S`, the forward orientation).
#[test]
fn test_simp_only_reversed_argument_rewrites_right_to_left() {
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\n\
         theorem t (hb : B) (rule : B = A) : A := by simp only [← rule]; exact hb\n",
        "reversed simp argument",
    );
}

/// The ASCII spelling `<-`, which reaches the lexer as two tokens and used to
/// reach `self.expr()` unconsumed.
#[test]
fn test_simp_only_ascii_reversed_argument_rewrites_right_to_left() {
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\n\
         theorem t (hb : B) (rule : B = A) : A := by simp only [<- rule]; exact hb\n",
        "ASCII-reversed simp argument",
    );
}

/// `←` on a GLOBAL equation, the `Injective.linearOrder` / `not_xor` shape.
#[test]
fn test_simp_only_reversed_global_argument_rewrites_right_to_left() {
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\naxiom hb : B\naxiom rule : B = A\n\
         theorem t : A := by\n  simp only [← rule]\n  exact hb\n",
        "reversed global simp argument",
    );
}

// ---------------------------------------------------------------------------
// The `-` modifier — a REFUSAL pin
// ---------------------------------------------------------------------------

/// `simp only [-plain]` asks simp to REMOVE `plain` from its set. Clean used
/// to eat the `-` and ADD it, closing a goal pinned v4.30.0-rc2 refuses
/// ("`simp` made no progress", plus "`plain` does not have the `[simp]`
/// attribute"). `plain` deliberately carries NO `@[simp]`, so a name that is
/// in no registry cannot close the goal by being excluded — only by being
/// added.
#[test]
fn test_simp_only_erased_argument_is_not_added_to_the_set() {
    assert_last_failed(
        "axiom A : Prop\naxiom B : Prop\naxiom hb : B\naxiom plain : A = B\n\
         theorem t : A := by\n  simp only [-plain]\n  exact hb\n",
        "erased simp argument",
    );
}

/// The control for the refusal above: the SAME list without the `-` closes, so
/// the refusal is attributable to the modifier and not to a broken fixture.
#[test]
fn test_the_same_argument_without_the_minus_still_closes() {
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\naxiom hb : B\naxiom plain : A = B\n\
         theorem t : A := by\n  simp only [plain]\n  exact hb\n",
        "erase control",
    );
}

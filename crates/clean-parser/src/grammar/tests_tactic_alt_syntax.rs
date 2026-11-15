// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for the Lean 4.8 tactic/term forms trust-ir's
//! `lean/trust_ir-semantics` package uses and Clean used to fail to parser
//! recovery (each row's source shape is quoted from that package):
//!
//! - `cases h : e with …` — `casesTarget := atomic(ident " : ")? term`;
//! - the column of an alternative's / a `( … )` block's first tactic bounds
//!   the term arguments of the tactics in it (`tacticSeq` = `sepByIndent`);
//! - `case some.cons hd tl =>` — a dotted case tag is one `ident`;
//! - `simp only [↓reduceIte]` — the `simpPre` / `simpPost` markers;
//! - `solve`, several alternative left-hand sides, `first` bounded by its
//!   column, and the tactic `match h : e with`.
//!
//! The term, pattern and `do` forms of the same package are in
//! `tests_term_alt_syntax.rs`, which shares the helpers below. Every
//! accepting row has a twin that Lean 4.8 also refuses.

#![allow(clippy::unwrap_used)]

use super::*;
use crate::{SimpPhase, SurfaceSimpArg};

/// The declarations of `src`, asserting that NO recovery happened anywhere —
/// neither a declaration-level `RawDecl` (checked by the callers) nor a
/// tactic-block recovery, which leaves no `RawDecl` but a diagnostic.
pub(super) fn decls_of(src: &str) -> Vec<SurfaceDecl> {
    let report = crate::parse_file_with_diagnostics(src).expect("source should parse");
    assert!(
        report.diagnostics.is_empty(),
        "no parser recovery expected: {:#?}",
        report.diagnostics
    );
    report.decls
}

pub(super) fn raw_count(decls: &[SurfaceDecl]) -> usize {
    decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count()
}

/// The tactic block of the single theorem in `src`, asserting no recovery.
fn tactics_of(src: &str) -> Vec<SurfaceTactic> {
    let decls = decls_of(src);
    assert_eq!(
        raw_count(&decls),
        0,
        "no parser recovery expected: {decls:#?}"
    );
    let theorems: Vec<_> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Theorem { proof, .. } => Some(proof),
            _ => None,
        })
        .collect();
    assert_eq!(
        theorems.len(),
        1,
        "expected exactly one theorem: {decls:#?}"
    );
    match theorems[0].as_ref() {
        SurfaceExpr::ByTactic(_, tactics) => tactics.clone(),
        other => panic!("expected a ByTactic proof, got {other:?}"),
    }
}

/// `src` must NOT parse cleanly: a hard error, a declaration-level recovery
/// placeholder, or a tactic-block recovery (which mints no `RawDecl`, only a
/// recovery diagnostic and a synthetic-sorry block).
pub(super) fn assert_refused(src: &str, what: &str) {
    match crate::parse_file_with_diagnostics(src) {
        Err(_) => {}
        Ok(report) => assert!(
            raw_count(&report.decls) > 0 || !report.diagnostics.is_empty(),
            "{what} must be refused (Lean 4.8 rejects it), got {:#?}",
            report.decls
        ),
    }
}

pub(super) fn name(text: &str) -> crate::SurfaceName {
    crate::SurfaceName::generated_path(text)
}

// --- `cases h : e` -------------------------------------------------------

#[test]
fn test_cases_named_target_records_equation_name() {
    let tactics = tactics_of(
        "theorem t (f : Nat → Option Nat) (n : Nat) : f n = f n := by\n  \
         cases hLookup : f n with\n  | none => rfl\n  | some v => rfl\n",
    );
    let SurfaceTactic::Cases(_, Some(hyp), target, alts) = &tactics[0] else {
        panic!("expected `cases h : e`, got {:?}", tactics[0]);
    };
    assert_eq!(hyp, &name("hLookup"));
    assert!(
        matches!(target.as_ref(), SurfaceExpr::App(..)),
        "{target:?}"
    );
    let names: Vec<_> = alts.iter().map(|a| a.name.clone()).collect();
    assert_eq!(names, vec![name("none"), name("some")]);
    assert_eq!(alts[1].args, vec![name("v")]);
}

#[test]
fn test_cases_named_target_without_alternatives_then_seq_focus() {
    // `cases h : s.lookupValue id <;> simp [...]` (AggregateProps.lean:826).
    let tactics = tactics_of("theorem t (o : Option Nat) : o = o := by\n  cases h : o <;> rfl\n");
    let SurfaceTactic::SeqFocus(_, lhs, _) = &tactics[0] else {
        panic!("expected `<;>`, got {:?}", tactics[0]);
    };
    assert!(
        matches!(lhs.as_ref(), SurfaceTactic::Cases(_, Some(h), _, alts) if *h == name("h") && alts.is_empty()),
        "{lhs:?}"
    );
}

#[test]
fn test_cases_plain_target_has_no_equation_name() {
    let tactics = tactics_of("theorem t (o : Option Nat) : o = o := by\n  cases o <;> rfl\n");
    let SurfaceTactic::SeqFocus(_, lhs, _) = &tactics[0] else {
        panic!("expected `<;>`, got {:?}", tactics[0]);
    };
    assert!(
        matches!(lhs.as_ref(), SurfaceTactic::Cases(_, None, _, _)),
        "{lhs:?}"
    );
}

#[test]
fn test_induction_named_target_is_refused() {
    // `induction` takes plain `term,+` targets in Lean 4.8: `h :` is a syntax
    // error there, and must stay one here.
    assert_refused(
        "theorem t (n : Nat) : n = n := by\n  induction h : n with\n  | zero => rfl\n  | succ k ih => rfl\n",
        "`induction h : n`",
    );
}

// --- an alternative's own column -----------------------------------------

#[test]
fn test_alternative_body_term_argument_stops_at_sibling_tactic() {
    // `exact h` then `cases m k with` at the same column inside an `induction`
    // alternative: two tactics, and the nested `cases` keeps both arms.
    let tactics = tactics_of(
        "theorem t (n : Nat) (m : Nat → Option Nat) (h : n = n) : n = n := by\n  \
         induction n with\n  | zero => rfl\n  | succ k ih =>\n    exact h\n    \
         cases m k with\n    | none => rfl\n    | some b => rfl\n",
    );
    let SurfaceTactic::Induction { alts, .. } = &tactics[0] else {
        panic!("expected induction, got {:?}", tactics[0]);
    };
    assert_eq!(alts.len(), 2);
    let succ = &alts[1].tactics;
    assert_eq!(
        succ.len(),
        2,
        "`exact h` and `cases …` are siblings: {succ:#?}"
    );
    let SurfaceTactic::Cases(_, None, _, inner) = &succ[1] else {
        panic!("expected the nested cases, got {:?}", succ[1]);
    };
    assert_eq!(inner.len(), 2);
}

#[test]
fn test_alternative_body_line_left_of_first_tactic_ends_the_alternative() {
    // Lean's `checkColEq`: a line left of the alternative's first tactic is
    // NOT part of that alternative — here it is the outer block's next tactic.
    let tactics = tactics_of(
        "theorem t (o : Option Nat) : o = o := by\n  cases o with\n  \
         | none => skip\n  | some v => skip\n  rfl\n",
    );
    assert_eq!(tactics.len(), 2, "`rfl` follows the cases: {tactics:#?}");
    let SurfaceTactic::Cases(_, None, _, alts) = &tactics[0] else {
        panic!("expected cases, got {:?}", tactics[0]);
    };
    assert_eq!(alts[1].tactics.len(), 1, "{:#?}", alts[1].tactics);
}

#[test]
fn test_paren_tactic_block_term_argument_stops_at_bullet() {
    // `(refine ite_pnl ?_ ?_\n · cases … with …)` (TransformCorrectness.lean:552).
    let tactics = tactics_of(
        "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  \
         (refine And.intro ?_ ?_\n   · exact hp\n   · exact hq)\n",
    );
    let SurfaceTactic::Paren(_, inner) = &tactics[0] else {
        panic!("expected a paren block, got {:?}", tactics[0]);
    };
    assert_eq!(inner.len(), 3, "refine + two bullets: {inner:#?}");
}

// --- `case some.cons` ----------------------------------------------------

#[test]
fn test_case_dotted_tag_is_one_name() {
    let tactics = tactics_of(
        "theorem t (o : Option Nat) (l : List Nat) : o = o := by\n  \
         cases o <;> cases l\n  case some.cons hd tl => rfl\n  all_goals rfl\n",
    );
    let SurfaceTactic::Case(_, tag, binders, _) = &tactics[1] else {
        panic!("expected case, got {:?}", tactics[1]);
    };
    assert_eq!(tag, &name("some.cons"));
    assert_eq!(binders, &vec![name("hd"), name("tl")]);
}

#[test]
fn test_case_tag_with_spaced_dot_is_refused() {
    // `some . cons` is not one identifier.
    assert_refused(
        "theorem t (o : Option Nat) : o = o := by\n  cases o\n  case some . cons => rfl\n  all_goals rfl\n",
        "`case some . cons`",
    );
}

// --- `↓` / `↑` simp markers ----------------------------------------------

fn simp_lemmas(tactic: &SurfaceTactic) -> Vec<SurfaceSimpArg> {
    match tactic {
        SurfaceTactic::Simp { lemmas, .. } => lemmas.clone(),
        other => panic!("expected simp, got {other:?}"),
    }
}

#[test]
fn test_simp_pre_post_markers_leave_the_rule() {
    let tactics = tactics_of(
        "theorem t (a b : Nat) : (if False then a else b) = b := by\n  \
         simp only [Bool.false_eq_true, ↓reduceIte, ↑ite_false, ↓← h]\n",
    );
    let lemmas = simp_lemmas(&tactics[0]);
    assert_eq!(lemmas.len(), 4);
    let rule_name = |arg: &SurfaceSimpArg| match &arg.term {
        SurfaceExpr::Ident(_, rule) => rule.clone(),
        other => panic!("expected a named rule, got {other:?}"),
    };
    assert_eq!(rule_name(&lemmas[1]), name("reduceIte"));
    assert_eq!(rule_name(&lemmas[2]), name("ite_false"));
    assert!(lemmas[3].reverse, "`↓← h` is a reversed rule");
    // The marker is recorded, so the elaborator can refuse a marked rule
    // that names nothing (Lean: "unknown identifier").
    let phases: Vec<_> = lemmas.iter().map(|arg| arg.phase).collect();
    assert_eq!(
        phases,
        vec![
            None,
            Some(SimpPhase::Pre),
            Some(SimpPhase::Post),
            Some(SimpPhase::Pre)
        ]
    );
}

#[test]
fn test_grind_parameter_with_simp_phase_marker_is_refused() {
    // `simpPre`/`simpPost` are `simpLemma` syntax; `grind`'s parameter
    // grammar has no such marker, so the list must not drop one silently.
    assert_refused(
        "theorem t (a : Nat) : a = a := by\n  grind [↓Nat.add_zero]\n",
        "`grind [↓Nat.add_zero]`",
    );
}

#[test]
fn test_simp_marker_without_rule_is_refused() {
    // `simpPre`/`simpPost` take a `term` after them: `]` and `*` are not one.
    assert_refused("theorem t : True := by\n  simp [↓]\n", "`simp [↓]`");
    assert_refused("theorem t : True := by\n  simp [↓*]\n", "`simp [↓*]`");
}

#[test]
fn test_simp_marker_then_minus_is_a_term_not_an_erase() {
    // Lean parses `↓-foo` as the rule `-foo` (and fails to elaborate it); it
    // is never `simpErase`.
    let tactics = tactics_of("theorem t : True := by\n  simp [↓-foo]\n");
    let lemmas = simp_lemmas(&tactics[0]);
    assert_eq!(lemmas.len(), 1);
    assert!(!lemmas[0].erase, "{:?}", lemmas[0]);
}

// --- alternative binders that spell a tactic -----------------------------

#[test]
fn test_alternative_binder_named_like_a_tactic_is_a_binder() {
    // `| BinOp op ty lhs rhs =>` (TransformCorrectness.lean): `lhs`/`rhs` are
    // conv tactics, but alternative binders are plain `ident`s.
    let tactics = tactics_of(
        "theorem t (i : Nat × Nat) : True := by\n  cases i with\n  | mk lhs rhs => trivial\n",
    );
    let SurfaceTactic::Cases(_, None, _, alts) = &tactics[0] else {
        panic!("expected cases, got {:?}", tactics[0]);
    };
    assert_eq!(alts[0].args, vec![name("lhs"), name("rhs")]);
}

#[test]
fn test_alternative_binder_lean_keyword_is_refused() {
    // `at` is a Lean 4.8 keyword: never an `ident`.
    assert_refused(
        "theorem t (i : Nat × Nat) : True := by\n  cases i with\n  | mk at rhs => trivial\n",
        "`| mk at rhs`",
    );
}

// --- `solve` -------------------------------------------------------------

#[test]
fn test_solve_desugars_to_focus_first_with_done() {
    let tactics = tactics_of(
        "theorem t (p q : Prop) (hq : q) : p ∨ q := by\n  solve\n  | exact Or.inl hq\n  \
         | exact Or.inr hq\n",
    );
    let SurfaceTactic::Focus(_, inner) = &tactics[0] else {
        panic!("expected focus, got {:?}", tactics[0]);
    };
    let SurfaceTactic::First(_, branches) = &inner[0] else {
        panic!("expected first, got {:?}", inner[0]);
    };
    assert_eq!(branches.len(), 2);
    for branch in branches {
        assert!(
            matches!(branch.last(), Some(SurfaceTactic::Named { name, args, .. })
                if name == "done" && args.is_empty()),
            "every branch ends in `done`: {branch:?}"
        );
    }
}

#[test]
fn test_solve_without_alternatives_is_refused() {
    assert_refused("theorem t : True := by\n  solve\n", "`solve` with no `|`");
}

// --- several left-hand sides, `first` bounded by its column --------------

#[test]
fn test_alternative_with_several_lhs_expands_per_constructor() {
    // `| Add | Sub | Mul => simp …` (MetaTheorems.lean): Lean's
    // `expandInductionAlts?` gives each LHS the shared tactics.
    let tactics = tactics_of(
        "theorem t (o : Option Nat) : o = o := by\n  cases o with\n  | none | some => rfl\n",
    );
    let SurfaceTactic::Cases(_, None, _, alts) = &tactics[0] else {
        panic!("expected cases, got {:?}", tactics[0]);
    };
    let names: Vec<_> = alts.iter().map(|a| a.name.clone()).collect();
    assert_eq!(names, vec![name("none"), name("some")]);
    assert!(alts.iter().all(|a| a.tactics.len() == 1), "{alts:#?}");
}

#[test]
fn test_first_stops_at_a_pipe_left_of_its_own() {
    // `| some l => … first | a | b` then `| none =>` of the enclosing cases.
    let tactics = tactics_of(
        "theorem t (o : Option Nat) : o = o := by\n  cases o with\n  | some l =>\n    \
         first\n      | rfl\n      | rfl\n  | none => rfl\n",
    );
    let SurfaceTactic::Cases(_, None, _, alts) = &tactics[0] else {
        panic!("expected cases, got {:?}", tactics[0]);
    };
    assert_eq!(alts.len(), 2, "`| none` belongs to the cases: {alts:#?}");
    let SurfaceTactic::First(_, branches) = &alts[0].tactics[0] else {
        panic!("expected first, got {:?}", alts[0].tactics[0]);
    };
    assert_eq!(branches.len(), 2);
}

// --- tactic `match h : e with` -------------------------------------------

#[test]
fn test_tactic_match_annotated_discriminant_records_its_name() {
    let tactics = tactics_of(
        "theorem t (xs : List Nat) : xs = xs := by\n  match hxs : xs with\n  \
         | [] => rfl\n  | y :: ys => rfl\n",
    );
    let SurfaceTactic::Match(_, Some(hyp), discrs, arms) = &tactics[0] else {
        panic!("expected `match h : e`, got {:?}", tactics[0]);
    };
    assert_eq!(hyp, &name("hxs"));
    assert_eq!((discrs.len(), arms.len()), (1, 2));
}

#[test]
fn test_tactic_match_second_annotated_discriminant_is_refused_loudly() {
    // Lean accepts this; Clean refuses it rather than drop an equation.
    assert_refused(
        "theorem t (a b : Nat) : a = a := by\n  match ha : a, hb : b with\n  | _, _ => rfl\n",
        "two annotated discriminants",
    );
}

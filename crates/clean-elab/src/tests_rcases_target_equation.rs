// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rcases casesTarget,* (with rcasesPatLo)?` with `h : e` targets and
//! several targets (`Init/RCases.lean`, `Lean/Elab/Tactic/RCases.lean`
//! `RCases.rcases`): a named target is generalized in the goal and every
//! branch gets `h : e = <pattern instance>`; several targets share the
//! pattern's tuple components. Trust-ir gap G24
//! (`Proofs/MemorySafety.lean:727`, `rcases hp : s.lookupValue ptrId with _ |
//! ptrVal`), ledger class (93).
//!
//! Ground-truthed on the pinned v4.8.0 `lean` binary (2026-10-08): every
//! accepted fixture elaborates there as written, and every refused one is
//! refused there (`type mismatch` for the equation used backwards, in the
//! wrong branch or for the wrong target; `The rfl tactic failed` for a
//! wrong-branch goal).

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

const LOOK: &str = "def look (n : Nat) : Option Nat := if n = 0 then none else some n\n";

fn elab(src: &str) -> Option<String> {
    let mut env = Environment::with_prelude();
    let text = format!("{LOOK}{src}");
    let decls = parse_file(&text).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(&mut env, d) {
            return Some(format!("{e} | {e:?}"));
        }
    }
    None
}

fn accepts(src: &str, what: &str) {
    if let Some(e) = elab(src) {
        panic!("{what} (pinned Lean 4.8.0 accepts):\n{src}\n--- got: {e}");
    }
}

/// `src` is refused, and for the reason the fixture is about: the error
/// mentions `reason` (case-insensitively), so an unrelated failure — a
/// prelude lookup, a parse recovery — cannot keep the refusal green.
fn refuses(src: &str, what: &str, reason: &str) {
    let Some(e) = elab(src) else {
        panic!("{what} (pinned Lean 4.8.0 refuses) was accepted:\n{src}");
    };
    assert!(
        e.to_lowercase().contains(&reason.to_lowercase()),
        "{what}: refused, but not for `{reason}`:\n{src}\n--- got: {e}"
    );
}

#[test]
fn test_rcases_named_target_is_generalized_in_the_goal() {
    accepts(
        "theorem a1 (n : Nat) : look n = none ∨ ∃ v, look n = some v := by\n\
         \x20 rcases hp : look n with _ | v\n\
         \x20 · exact Or.inl rfl\n\
         \x20 · exact Or.inr ⟨v, rfl⟩\n",
        "each branch's goal reads the constructor instance",
    );
}

#[test]
fn test_rcases_named_target_records_the_equation_left_to_right() {
    accepts(
        "theorem a2 (n : Nat) (h : look n = some 3) : look n ≠ none := by\n\
         \x20 rcases hp : look n with _ | v\n\
         \x20 · exact absurd (hp.symm.trans h) (fun e => nomatch e)\n\
         \x20 · exact fun e => nomatch e\n",
        "the none branch refutes `h` through `hp`",
    );
    accepts(
        "theorem a3 (n : Nat) : True := by\n\
         \x20 rcases hp : look n with _ | v\n\
         \x20 · have _e : look n = none := hp\n\
         \x20   trivial\n\
         \x20 · have _e : look n = some v := hp\n\
         \x20   trivial\n",
        "`hp : look n = <instance>` in each branch",
    );
}

#[test]
fn test_rcases_named_local_target_and_single_name_pattern() {
    accepts(
        "theorem a4 (o : Option Nat) (k : Nat) (h : o = some k) : o ≠ none := by\n\
         \x20 rcases ho : o with _ | v\n\
         \x20 · exact absurd (ho.symm.trans h) (fun e => nomatch e)\n\
         \x20 · exact fun e => nomatch e\n",
        "a named LOCAL target is generalized too",
    );
    accepts(
        "theorem a5 (n : Nat) : look n = look n := by\n\
         \x20 rcases hp : look n with y\n\
         \x20 have _e : look n = y := hp\n\
         \x20 rfl\n",
        "a name pattern names the generalized variable",
    );
    accepts(
        "theorem a8 (h : Nat) (n : Nat) : True := by\n\
         \x20 rcases h : look n with _ | v\n\
         \x20 · have _e : look n = none := h\n\
         \x20   trivial\n\
         \x20 · have _e : look n = some v := h\n\
         \x20   trivial\n",
        "the equation shadows an older local of its name",
    );
}

#[test]
fn test_rcases_several_targets_share_the_tuple_pattern() {
    accepts(
        "theorem a6 (p q r s : Prop) (h1 : p ∧ q) (h2 : r ∧ s) : q ∧ r := by\n\
         \x20 rcases h1, h2 with ⟨⟨_, hq⟩, hr, _⟩\n\
         \x20 exact ⟨hq, hr⟩\n",
        "the last target takes the surplus components as a tuple",
    );
    accepts(
        "theorem a7 (n m : Nat) : look m = look m := by\n\
         \x20 rcases hn : look n, hm : look m with ⟨_ | x, y⟩\n\
         \x20 · have _e1 : look n = none := hn\n\
         \x20   have _e2 : look m = y := hm\n\
         \x20   rfl\n\
         \x20 · have _e1 : look n = some x := hn\n\
         \x20   have _e2 : look m = y := hm\n\
         \x20   rfl\n",
        "each named target records its own equation",
    );
}

#[test]
fn test_rcases_named_target_equation_misuse_is_refused() {
    refuses(
        "theorem r1 (n : Nat) : True := by\n\
         \x20 rcases hp : look n with _ | v\n\
         \x20 · trivial\n\
         \x20 · have _e : some v = look n := hp\n\
         \x20   trivial\n",
        "the equation used backwards",
        "type mismatch",
    );
    refuses(
        "theorem r2 (n : Nat) : True := by\n\
         \x20 rcases hp : look n with _ | v\n\
         \x20 · have _e : look n = some 0 := hp\n\
         \x20   trivial\n\
         \x20 · trivial\n",
        "the some-branch equation claimed in the none branch",
        "type mismatch",
    );
    refuses(
        "theorem r3 (n m : Nat) : True := by\n\
         \x20 rcases hn : look n, hm : look m with ⟨_ | x, y⟩\n\
         \x20 · trivial\n\
         \x20 · have _e : look m = some x := hn\n\
         \x20   trivial\n",
        "one target's equation claimed about the other",
        "type mismatch",
    );
    refuses(
        "theorem r4 (n : Nat) : look n = none := by\n\
         \x20 rcases hp : look n with _ | v\n\
         \x20 · rfl\n\
         \x20 · rfl\n",
        "the some branch's goal is `some v = none`",
        "rfl",
    );
}

/// `finish` clears a `-` component with its dependents (`tryClearMany'`),
/// and the equation is already in the context then, so it goes too (pinned
/// Lean 4.8.0: `unknown identifier 'h'`); the `none` branch keeps its own.
#[test]
fn test_rcases_cleared_field_takes_its_equation() {
    accepts(
        "theorem c0 (n : Nat) : True := by\n\
         \x20 rcases h : look n with _ | -\n\
         \x20 · have _e : look n = none := h\n\
         \x20   trivial\n\
         \x20 · trivial\n",
        "the none branch has no cleared field and keeps `h`",
    );
    refuses(
        "theorem c1 (n : Nat) : True := by\n\
         \x20 rcases h : look n with _ | -\n\
         \x20 · trivial\n\
         \x20 · have _e := h\n\
         \x20   trivial\n",
        "the cleared field's equation is cleared with it",
        "unknown identifier",
    );
}

/// Several named targets are generalized TOGETHER (`generalizeCore`): each
/// equation states its ORIGINAL term, so an earlier target is never
/// abstracted inside a later target's equation (`hb : look n = …`, never
/// `look m = …`).
#[test]
fn test_rcases_several_named_targets_keep_their_original_terms() {
    accepts(
        "theorem e02 (n : Nat) : True := by\n\
         \x20 rcases ha : n, hb : look n with ⟨m, _ | v⟩\n\
         \x20 · have _x : look n = none := hb\n\
         \x20   have _y : n = m := ha\n\
         \x20   trivial\n\
         \x20 · have _x : look n = some v := hb\n\
         \x20   trivial\n",
        "the later equation keeps the earlier target's term",
    );
    accepts(
        "theorem e05 (n : Nat) : look n = look n := by\n\
         \x20 rcases ha : n, hb : look n with ⟨m, w⟩\n\
         \x20 have _x : look n = w := hb\n\
         \x20 have _y : n = m := ha\n\
         \x20 rfl\n",
        "both equations on their original terms, no split",
    );
    refuses(
        "theorem e01 (n : Nat) : True := by\n\
         \x20 rcases ha : n, hb : look n with ⟨m, _ | v⟩\n\
         \x20 · have _x : look m = none := hb\n\
         \x20   trivial\n\
         \x20 · trivial\n",
        "the earlier target abstracted inside the later equation",
        "type mismatch",
    );
    refuses(
        "theorem e04 (n : Nat) : look n = look n := by\n\
         \x20 rcases ha : n, hb : look n with ⟨m, w⟩\n\
         \x20 have _x : look m = w := hb\n\
         \x20 rfl\n",
        "the earlier target abstracted inside the later equation, no split",
        "type mismatch",
    );
}

/// Without `with`, the pattern is `⟨⟩` (`evalRCases`: `RCasesPatt.tuple tk
/// []`), which splits one target ONE level, every field `_`, and refuses a
/// type that is not an inductive.
#[test]
fn test_rcases_without_with_splits_one_level() {
    accepts(
        "theorem p04 (n : Nat) : look n = look n := by\n\
         \x20 rcases hp : look n\n\
         \x20 · have _e : look n = none := hp\n\
         \x20   rfl\n\
         \x20 · rfl\n",
        "a named target splits into its two constructors",
    );
    accepts(
        "theorem p11 (a b : Prop) (h : a ∨ b) : True := by\n\
         \x20 rcases h\n\
         \x20 · trivial\n\
         \x20 · trivial\n",
        "a local `Or` splits into two goals",
    );
    accepts(
        "theorem f1 (h : False) : 1 = 2 := by\n\
         \x20 rcases h\n",
        "`False` splits into no goals",
    );
    accepts(
        "theorem f3 (a b : Prop) (h : a ∧ b) : b := by\n\
         \x20 rcases h\n\
         \x20 assumption\n",
        "an `And` is destructured, its fields unnamed",
    );
    refuses(
        "theorem p03 (n : Nat) : look n = look n := by\n\
         \x20 rcases hp : look n\n\
         \x20 rfl\n",
        "the `some` goal is left open",
        "unsolved",
    );
    refuses(
        "theorem p10 (a b : Prop) (h : a ∨ b) : True := by\n\
         \x20 rcases h\n\
         \x20 trivial\n",
        "the `inr` goal is left open",
        "unsolved",
    );
    refuses(
        "theorem f2 (p : Prop) (h : p) : p := by\n\
         \x20 rcases h\n\
         \x20 exact h\n",
        "a hypothesis that is not an inductive",
        "not an inductive datatype",
    );
}

/// The later targets are destructured in every goal the first one produced,
/// one goal at a time (`rcasesContinue`), and the goals come out in
/// lexicographic order.
#[test]
fn test_rcases_several_targets_split_in_every_branch() {
    accepts(
        "theorem s05 (a b c d : Prop) (h1 : a ∨ b) (h2 : c ∨ d) : (a ∨ b) ∧ (c ∨ d) := by\n\
         \x20 rcases h1, h2 with ⟨x | x, y | y⟩\n\
         \x20 · exact ⟨Or.inl x, Or.inl y⟩\n\
         \x20 · exact ⟨Or.inl x, Or.inr y⟩\n\
         \x20 · exact ⟨Or.inr x, Or.inl y⟩\n\
         \x20 · exact ⟨Or.inr x, Or.inr y⟩\n",
        "two `Or` locals give four goals",
    );
    accepts(
        "theorem u03 (a b c d : Prop) (h1 : a ∨ b) (h2 : c ∧ d) : c := by\n\
         \x20 rcases h1, h2 with ⟨x | z, y, y2⟩\n\
         \x20 · exact y\n\
         \x20 · exact y\n",
        "the second target's tuple is applied to IT in both branches",
    );
    accepts(
        "theorem s01 (n m : Nat) : True := by\n\
         \x20 rcases hn : look n, hm : look m with ⟨_ | x, _ | y⟩\n\
         \x20 · have _a : look n = none := hn\n\
         \x20   have _b : look m = none := hm\n\
         \x20   trivial\n\
         \x20 · have _a : look n = none := hn\n\
         \x20   have _b : look m = some y := hm\n\
         \x20   trivial\n\
         \x20 · have _a : look n = some x := hn\n\
         \x20   have _b : look m = none := hm\n\
         \x20   trivial\n\
         \x20 · have _a : look n = some x := hn\n\
         \x20   have _b : look m = some y := hm\n\
         \x20   trivial\n",
        "two named targets, both split, each goal with both equations",
    );
    refuses(
        "theorem s04n (a b c d : Prop) (h1 : a ∨ b) (h2 : c ∨ d) : True := by\n\
         \x20 rcases h1, h2 with ⟨x | x, y | y⟩\n\
         \x20 · trivial\n\
         \x20 · trivial\n\
         \x20 · trivial\n",
        "the fourth goal is left open",
        "unsolved",
    );
    refuses(
        "theorem s05n (a b c d : Prop) (h1 : a ∨ b) (h2 : c ∨ d) : (a ∨ b) ∧ (c ∨ d) := by\n\
         \x20 rcases h1, h2 with ⟨x | x, y | y⟩\n\
         \x20 · exact ⟨Or.inl x, Or.inl y⟩\n\
         \x20 · exact ⟨Or.inr x, Or.inl y⟩\n\
         \x20 · exact ⟨Or.inl x, Or.inr y⟩\n\
         \x20 · exact ⟨Or.inr x, Or.inr y⟩\n",
        "the second goal is `inl.inr`, not `inr.inl`",
        "mismatch",
    );
    refuses(
        "theorem s01n (n m : Nat) : True := by\n\
         \x20 rcases hn : look n, hm : look m with ⟨_ | x, _ | y⟩\n\
         \x20 · trivial\n\
         \x20 · have _b : look m = some y := hm\n\
         \x20   trivial\n\
         \x20 · have _b : look m = some x := hm\n\
         \x20   trivial\n\
         \x20 · trivial\n",
        "the third goal's `hm` reads `look m = none`",
        "type mismatch",
    );
}

/// A typed pattern on a named target types the target (`Term.elabTerm tgt
/// ty`): `rcases h : 0 with (x : Int)` has `h : (0 : Int) = x`.
#[test]
fn test_rcases_named_target_typed_pattern_types_the_target() {
    accepts(
        "theorem p09 : True := by\n\
         \x20 rcases h : 0 with (x : Int)\n\
         \x20 have _e : (0 : Int) = x := h\n\
         \x20 trivial\n",
        "the target elaborated at the pattern's type",
    );
    refuses(
        "theorem p09n : True := by\n\
         \x20 rcases h : 0 with (x : Int)\n\
         \x20 have _e : (0 : Nat) = 0 := h\n\
         \x20 trivial\n",
        "the equation is about an `Int`",
        "type mismatch",
    );
}

/// An unnamed target that is not a local is generalized too
/// (`generalizeExceptFVar`): its occurrences in the goal's target become the
/// pattern's instance, and hypotheses that mention it are left alone.
#[test]
fn test_rcases_unnamed_term_target_is_generalized_in_the_goal() {
    accepts(
        "theorem b2 (n : Nat) : look n = none ∨ ∃ v, look n = some v := by\n\
         \x20 rcases look n with _ | v\n\
         \x20 · exact Or.inl rfl\n\
         \x20 · exact Or.inr ⟨v, rfl⟩\n",
        "each branch's goal reads the constructor instance",
    );
    accepts(
        "theorem b3 (p : Prop) : p ∨ ¬p := by\n\
         \x20 rcases Classical.em p with h | h\n\
         \x20 · exact Or.inl h\n\
         \x20 · exact Or.inr h\n",
        "a proof term target that the goal does not mention",
    );
    accepts(
        "theorem b4 (n m : Nat) (h : look m = some 1) : look n = look n := by\n\
         \x20 rcases look n, h with ⟨_ | v, -⟩\n\
         \x20 · rfl\n\
         \x20 · rfl\n",
        "a term target beside a local one",
    );
    refuses(
        "theorem b1 (P : Option Nat → Prop) (n : Nat) (h : P (look n)) : P (look n) := by\n\
         \x20 rcases look n with _ | v\n\
         \x20 · exact h\n\
         \x20 · exact h\n",
        "the goal is `P none`, and `h` still mentions `look n`",
        "mismatch",
    );
}

/// A generalization in a case of an earlier elimination mints its goal under
/// the PARENT's scope: the eliminated variable is gone from the context but
/// still bound above, and reusing its id resolved the new variable to it
/// (three levels under `all_goals`: kernel "expected Option Nat, got Nat").
/// Plain `generalize` + `cases` had the same capture before `rcases` used it.
#[test]
fn test_rcases_and_generalize_three_levels_deep_under_all_goals() {
    accepts(
        "theorem d3 (P : Option Nat → Prop) (h : ∀ o, P o) (a0 a1 a2 : Nat) :\n\
         \x20   P (look a0) ∧ P (look a1) ∧ P (look a2) := by\n\
         \x20 all_goals rcases look a0 with _ | v0\n\
         \x20 all_goals rcases look a1 with _ | v1\n\
         \x20 all_goals rcases look a2 with _ | v2\n\
         \x20 all_goals exact ⟨h _, h _, h _⟩\n",
        "eight goals, each generalized three times",
    );
    accepts(
        "theorem g3 (a0 a1 a2 : Nat) : True := by\n\
         \x20 all_goals generalize look a0 = x0\n\
         \x20 all_goals cases x0\n\
         \x20 all_goals generalize look a1 = x1\n\
         \x20 all_goals cases x1\n\
         \x20 all_goals generalize look a2 = x2\n\
         \x20 all_goals cases x2\n\
         \x20 all_goals exact True.intro\n",
        "plain `generalize` in every case of an earlier `cases`",
    );
    refuses(
        "theorem d3n (P : Option Nat → Prop) (h : ∀ o, P o) (a0 a1 a2 : Nat)\n\
         \x20   (hp : P (look a2)) : P (look a0) ∧ P (look a1) ∧ P (look a2) := by\n\
         \x20 all_goals rcases look a0 with _ | v0\n\
         \x20 all_goals rcases look a1 with _ | v1\n\
         \x20 all_goals rcases look a2 with _ | v2\n\
         \x20 all_goals exact ⟨h _, h _, hp⟩\n",
        "the third component is the case's instance, not `look a2`",
        "mismatch",
    );
    refuses(
        "theorem g3n (a0 a1 a2 : Nat) (P : Option Nat → Prop) (hp : P (look a2)) :\n\
         \x20   P (look a2) := by\n\
         \x20 all_goals generalize look a0 = x0\n\
         \x20 all_goals cases x0\n\
         \x20 all_goals generalize look a1 = x1\n\
         \x20 all_goals cases x1\n\
         \x20 all_goals generalize look a2 = x2\n\
         \x20 all_goals cases x2\n\
         \x20 all_goals exact hp\n",
        "the goal is `P none` / `P (some _)`, not `P (look a2)`",
        "mismatch",
    );
}

/// `⟨⟩` on an indexed family runs `cases`: an `Eq` with a variable side is
/// substituted, and one between constructor applications is split by
/// injection as Lean's `unifyEqs?` does (G82; before it, Clean's `cases`
/// could not eliminate it and `⟨⟩` kept the hypothesis, `rintro ⟨⟩ ⟨⟩ ⟨⟩` in
/// `Mathlib/Order/Basic.lean`'s `PartialOrder.toPreorder_injective`).
#[test]
fn test_rcases_without_with_on_an_equation() {
    accepts(
        "theorem i2 (n : Nat) (h : n = 5) : n = 5 := by\n\
         \x20 rcases h\n\
         \x20 rfl\n",
        "a variable side is substituted",
    );
    accepts(
        "structure Box where\n\
         \x20 x : Nat\n\
         theorem i1 (a b : Nat) (h : (⟨a⟩ : Box) = ⟨b⟩) : True := by\n\
         \x20 rcases h\n\
         \x20 trivial\n",
        "an equation of constructor applications is split by injection",
    );
}

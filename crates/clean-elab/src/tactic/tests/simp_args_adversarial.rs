// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial e2e pins for the `simpArg` seam — the near-miss shapes the
//! package's own fixtures do not reach.
//!
//! Every expectation below was ground-truthed against the pinned Lean binary
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`, and the
//! transcript is quoted at each test. The three families are:
//!
//! * `-lemma` now has a real writer (`SimpConfig::exclude`), so it must bite
//!   the `[*]` channel too — Lean's `applyStarArg` skips a hypothesis whose
//!   `.fvar` origin `isErased`;
//! * a `←` rule must survive every `simp_rw` LOCATION, not only the goal;
//! * the congruence spine must still rewrite two independent positions of a
//!   head that has a FROZEN one, including the `mk_congr` combination where
//!   the function side and the argument side both carry proofs.

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

// ---------------------------------------------------------------------------
// `-h` must also remove `h` from the `[*]` channel
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// axiom P : Prop
// example (h : P) : P := by simp [*]        -- accepted
// example (h : P) : P := by simp [*, -h]    -- error: `simp` made no progress
// ```
//
// Lean's `applyStarArg` loops `getPropHyps` guarded by
// `unless simpTheorems.isErased (.fvar h)`, so an erased local never joins the
// star set. `-` had no writer at all before this package, so the two channels
// could not disagree; now that it writes `SimpConfig::exclude`, the star
// collector has to read it.

/// The goal is a DISJUNCTION rather than `P` itself, deliberately: Clean's
/// simp runs an `assumption`-shaped closer that shuts `⊢ P` with `h : P` and
/// no rewrite at all (measured — the proof term came back as `fun h => h`), so
/// a bare `⊢ P` cannot discriminate. `⊢ P ∨ Q` closes only by rewriting `P` to
/// `True`, which is exactly the star rule.
const STAR_FIXTURE: &str = "\
axiom P : Prop
axiom Q : Prop
";

/// Control: the star alone closes the goal, so the refusal below is
/// attributable to the `-h` element and nothing else.
#[test]
fn test_simp_star_closes_a_goal_its_hypothesis_proves() {
    assert_last_closed(
        &format!("{STAR_FIXTURE}theorem t (h : P) : P ∨ Q := by simp [*]\n"),
        "simp [*] control",
    );
}

/// `simp [*, -h]` must NOT use `h`.
#[test]
fn test_simp_star_does_not_use_an_erased_hypothesis() {
    assert_last_failed(
        &format!("{STAR_FIXTURE}theorem t (h : P) : P ∨ Q := by simp [*, -h]\n"),
        "simp [*, -h]",
    );
}

/// The same for a named erasure of a hypothesis that the star would otherwise
/// turn into an EQUATION rule, the other half of `collect_hypothesis_lemmas`.
/// Pinned v4.30.0-rc2:
///
/// ```text
/// example (e : Q = P) (hp : P) : Q := by simp [*]        -- accepted
/// example (e : Q = P) (hp : P) : Q := by simp [*, -e]    -- no progress
/// ```
#[test]
fn test_simp_star_does_not_use_an_erased_equation_hypothesis() {
    assert_last_closed(
        "axiom P : Prop\naxiom Q : Prop\n\
         theorem ctl (e : Q = P) (hp : P) : Q := by simp [*]\n",
        "equation star control",
    );
    assert_last_failed(
        "axiom P : Prop\naxiom Q : Prop\n\
         theorem t (e : Q = P) (hp : P) : Q := by simp [*, -e]\n",
        "simp [*, -e]",
    );
}

// ---------------------------------------------------------------------------
// `←` on an `Iff`
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// axiom riff : B ↔ A
// example : A := by simp only [← riff]; exact hb   -- accepted
// example : A := by simp only [riff];   exact hb   -- error: no progress
// ```
//
// The `Iff` branch of `rules_from_proof` goes through `propext` and then
// re-orients with `Eq.symm` at `Prop`/`Level::zero()`; nothing else in the
// package exercises `←` over an iff.

const IFF_FIXTURE: &str = "\
axiom A : Prop
axiom B : Prop
axiom hb : B
axiom riff : B ↔ A
";

#[test]
fn test_simp_only_forward_iff_argument_does_not_close_the_reversed_goal() {
    assert_last_failed(
        &format!("{IFF_FIXTURE}theorem ctl : A := by\n  simp only [riff]\n  exact hb\n"),
        "forward iff control",
    );
}

#[test]
fn test_simp_only_reversed_iff_argument_rewrites_right_to_left() {
    assert_last_closed(
        &format!("{IFF_FIXTURE}theorem t : A := by\n  simp only [← riff]\n  exact hb\n"),
        "reversed iff simp argument",
    );
}

// ---------------------------------------------------------------------------
// `←` on a name that is a DEFINITION, not an equation
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2 throws rather than silently unfolding forward:
//
// ```
// def myId (n : Nat) : Nat := n
// example : myId 3 = 3 := by simp [← myId]
// -- error: Invalid `←` modifier: `myId` is a declaration name to be unfolded
// ```
//
// Clean must not close the goal by quietly using the forward unfold, which is
// what eating the `←` used to do.

#[test]
fn test_simp_reversed_definition_name_is_refused() {
    assert_last_failed(
        "def myId (n : Nat) : Nat := n\ntheorem t : myId 3 = 3 := by simp [← myId]\n",
        "← on a definition name",
    );
}

/// Control: the same list WITHOUT the `←` unfolds and closes, so the refusal
/// above is the modifier's doing and not a broken fixture.
#[test]
fn test_simp_forward_definition_name_still_unfolds() {
    assert_last_closed(
        "def myId (n : Nat) : Nat := n\ntheorem t : myId 3 = 3 := by simp [myId]\n",
        "forward definition unfold",
    );
}

// ---------------------------------------------------------------------------
// `simp_rw` keeps its `←` at EVERY location, not only the goal
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2 (spelled with `simp only`, which is what Mathlib's
// `simp_rw` desugars each rule to — `simp_rw` itself is Mathlib-only):
//
// ```
// example (hb : B) (rule : B = A) (h : A) : B := by
//   simp only [← rule] at h; exact h            -- accepted
// ```
//
// `compound_simp_rw` resolves its rules through `resolve_simp_args`, but the
// `Hyps` / `HypsAndGoal` / `Wildcard` arms used to forward only the by-NAME
// remainder, so every reversed or term-shaped rule was dropped at a
// hypothesis with no diagnostic — where the by-name path at least ran the
// rule (in the wrong direction).

const RW_FIXTURE: &str = "\
axiom A : Prop
axiom B : Prop
axiom C : Prop
";

#[test]
fn test_simp_rw_reversed_rule_rewrites_the_goal_right_to_left() {
    assert_last_failed(
        &format!(
            "{RW_FIXTURE}theorem ctl (hb : B) (rule : B = A) : A := by\n\
             \x20 simp_rw [rule]\n  exact hb\n"
        ),
        "forward simp_rw control",
    );
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (hb : B) (rule : B = A) : A := by\n\
             \x20 simp_rw [← rule]\n  exact hb\n"
        ),
        "reversed simp_rw rule",
    );
}

/// The `at h` location. `simp only [← rule] at h` is the control that the
/// fixture itself is sound.
#[test]
fn test_simp_only_reversed_rule_at_a_hypothesis_rewrites_it() {
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (rule : B = A) (h : A) : B := by\n\
             \x20 simp only [← rule] at h\n  exact h\n"
        ),
        "simp only [← rule] at h",
    );
}

#[test]
fn test_simp_rw_reversed_rule_at_a_hypothesis_is_not_dropped() {
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (rule : B = A) (h : A) : B := by\n\
             \x20 simp_rw [← rule] at h\n  exact h\n"
        ),
        "simp_rw [← rule] at h",
    );
}

/// A TERM-shaped `simp_rw` rule at a hypothesis. Before the package this was
/// a loud `resolve_ident` refusal; it must not become a silent no-op.
#[test]
fn test_simp_rw_applied_rule_at_a_hypothesis_is_not_dropped() {
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\naxiom ruleAt : Nat → A = B\n\
         theorem t (h : A) : B := by\n  simp_rw [ruleAt 0] at h\n  exact h\n",
        "simp_rw [ruleAt 0] at h",
    );
}

// ---------------------------------------------------------------------------
// The congruence spine still rewrites the INDEPENDENT positions
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// axiom D : (R : Prop) → (R → Prop) → Prop → Prop
// example : D P f Q0 := by simp only [hfg, hq]; exact hd    -- accepted
// ```
//
// Position 0 is frozen (`f`'s type mentions it), so this application is
// handled ENTIRELY by `simp_app_spine`. Positions 1 and 2 both move, which is
// the only shape that reaches the spine's `mk_congr` arm — the function side
// and the argument side each carrying a proof. The package's own fixtures move
// at most one position, so `mk_congr` was never exercised there.

const SPINE_FIXTURE: &str = "\
axiom P : Prop
axiom Q0 : Prop
axiom R0 : Prop
axiom hq : Q0 = R0
axiom f : P → Prop
axiom g : P → Prop
axiom hfg : f = g
axiom D : (R : Prop) → (R → Prop) → Prop → Prop
axiom hd : D P g R0
";

#[test]
fn test_simp_spine_rewrites_two_independent_positions_of_a_frozen_head() {
    assert_last_closed(
        &format!("{SPINE_FIXTURE}theorem t : D P f Q0 := by\n  simp only [hfg, hq]\n  exact hd\n"),
        "two independent positions under a frozen head",
    );
}

/// Negative control: with neither rule the goal does not close, so the pass
/// above is attributable to both rewrites landing.
#[test]
fn test_simp_spine_control_without_the_rules_does_not_close() {
    assert_last_failed(
        &format!("{SPINE_FIXTURE}theorem ctl : D P f Q0 := by\n  simp only []\n  exact hd\n"),
        "spine control",
    );
}

// ---------------------------------------------------------------------------
// The list is ORDERED: `-x` after `[x]` cancels it
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// axiom plain : A = B     -- no @[simp]
// example : A := by simp only [-plain, plain]; exact hb   -- accepted
// example : A := by simp only [plain, -plain]; exact hb   -- no progress
// ```
//
// `elabSimpArgs` walks the elements in order: the add arm runs
// `uneraseSimpEntry` before `addSimpEntry`, and the erase arm removes what an
// earlier element added. Two order-free sets accept both spellings.

const ORDER_FIXTURE: &str = "\
axiom A : Prop
axiom B : Prop
axiom hb : B
axiom plain : A = B
";

#[test]
fn test_simp_only_add_after_erase_puts_the_lemma_back() {
    assert_last_closed(
        &format!("{ORDER_FIXTURE}theorem t : A := by\n  simp only [-plain, plain]\n  exact hb\n"),
        "erase then add",
    );
}

#[test]
fn test_simp_only_erase_after_add_cancels_it() {
    assert_last_failed(
        &format!("{ORDER_FIXTURE}theorem t : A := by\n  simp only [plain, -plain]\n  exact hb\n"),
        "add then erase",
    );
}

// ---------------------------------------------------------------------------
// A term argument whose HOLE never reaches the pattern
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2 refuses `simp only [ruleAt _]` — "`simp` made no
// progress" — even though `simp only [ruleAt 0]` closes the same goal: the
// abstracted metavariable becomes a binder that the rewrite pattern `A` never
// determines. Clean's `abstract_open_metas` is `abstractMVars`, and the pin is
// here because the term path COULD have over-accepted, emitting a proof with
// an undetermined pattern variable in it.

#[test]
fn test_simp_only_argument_hole_the_pattern_cannot_determine_is_refused() {
    assert_last_failed(
        "axiom A : Prop\naxiom B : Prop\naxiom hb : B\naxiom ruleAt : Nat → A = B\n\
         theorem t : A := by\n  simp only [ruleAt _]\n  exact hb\n",
        "undetermined hole in a term argument",
    );
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\naxiom hb : B\naxiom ruleAt : Nat → A = B\n\
         theorem t : A := by\n  simp only [ruleAt 0]\n  exact hb\n",
        "determined argument control",
    );
}

// ---------------------------------------------------------------------------
// `←` survives `simpa`
// ---------------------------------------------------------------------------

/// `simpa [← rule] using hb`: `compound_simpa` shares `apply_simp_args` with
/// `simp`, and the reversed rule has to reach its goal simplification.
#[test]
fn test_simpa_reversed_argument_rewrites_right_to_left() {
    assert_last_closed(
        "axiom A : Prop\naxiom B : Prop\n\
         theorem t (hb : B) (rule : B = A) : A := by simpa [← rule] using hb\n",
        "simpa [← rule]",
    );
}

/// A `←` element whose term is a LOCAL of non-Prop type is refused, not
/// silently skipped — pinned v4.30.0-rc2 throws "Variable `n` is not a
/// proposition or let-declaration".
#[test]
fn test_simp_only_reversed_non_proposition_local_is_refused() {
    assert_last_failed(
        "axiom A : Prop\ntheorem t (n : Nat) (ha : A) : A := by\n  simp only [← n]\n  exact ha\n",
        "← on a non-proposition local",
    );
}

// ---------------------------------------------------------------------------
// `simpa [*]` is `simp [*]` plus a closing step
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// example (h : P) : P ∨ Q := by simpa [*] using True.intro   -- accepted
// ```
//
// `Parser::parse_tactic_simpa` bound `parse_simp_lemmas`' star flag to
// `_use_hypotheses` and threw it away, so `simpa [*]` ran with no hypothesis
// rules at all — the one entry point of the five sharing the lemma list that
// still could not see `[*]`.

#[test]
fn test_simpa_star_uses_the_prop_hypotheses() {
    assert_last_closed(
        &format!("{STAR_FIXTURE}theorem t (h : P) : P ∨ Q := by simpa [*] using True.intro\n"),
        "simpa [*]",
    );
}

/// Control: without the star the same `simpa` cannot close it, so the pass
/// above is attributable to the star reaching the simp set.
#[test]
fn test_simpa_without_the_star_cannot_close_the_same_goal() {
    assert_last_failed(
        &format!("{STAR_FIXTURE}theorem t (h : P) : P ∨ Q := by simpa using True.intro\n"),
        "simpa control",
    );
}

// ---------------------------------------------------------------------------
// Every LOCATION carries the resolved rule, not just the goal
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// example (rule : B = A) (h : A) : A := by
//   simp only [← rule] at h ⊢; exact h        -- accepted
// ```
//
// `simp` builds one config per location and both go through
// `apply_simp_args`; `simp_rw` resolves once and has to forward BOTH
// channels to each arm.

#[test]
fn test_simp_only_reversed_rule_at_hypothesis_and_goal() {
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (rule : B = A) (h : A) : A ∨ C := by\n\
             \x20 simp only [← rule] at h ⊢\n  exact Or.inl h\n"
        ),
        "simp only [← rule] at h ⊢",
    );
}

/// The `at *` arm of `simp_rw`, which walks the local context itself rather
/// than going through `simp_rw_hyps_outcome`. The goal is `A ∨ C` so that the
/// GOAL step also has something to rewrite: that arm ignores the hypothesis
/// results (`let _ = ...`) and reports the goal step's verdict, so a fixture
/// whose goal is already `B` reports `NoProgress` however well the
/// hypotheses went.
#[test]
fn test_simp_rw_reversed_rule_at_wildcard_reaches_the_hypotheses() {
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (rule : B = A) (h : A) : A ∨ C := by\n\
             \x20 simp_rw [← rule] at *\n  exact Or.inl h\n"
        ),
        "simp_rw [← rule] at *",
    );
}

// ---------------------------------------------------------------------------
// The two ORIGINAL congruence faces, at the real heads
// ---------------------------------------------------------------------------
//
// `simp_congr_arg_kinds.rs` pins the argument-kind analysis at a hand-built
// head `D : (R : Prop) → (R → Prop) → Prop → Prop`. The reported rows are at
// `@ite α c inst t e` and `@Exists α p`, and those two differ from `D` in
// ways the analysis can get wrong: `ite`'s dependent position is guarded by
// an INSTANCE sibling (`inst : Decidable c`) and reached only after
// `try_simp_ite` declines, and `Exists`' frozen position is the implicit TYPE
// argument, which is also where `simp_app_spine`'s "frozen ⇒ handle the whole
// node here" rule has to hold or the prefix `Exists Pc` is re-entered as its
// own node.
//
// Both close under pinned v4.30.0-rc2 (exit 0), which rewrites the condition
// soundly through `@[congr] ite_congr`. With that theorem imported, Clean
// transports the condition and its instance; a built-in-only environment
// without it preserves the condition and rewrites independent positions. What must
// NEVER happen again is the ill-typed term reaching the kernel — before the
// package these gave "expected `Decidable fvar#1`, got `Decidable fvar#0`"
// and "expected `True → Prop`, got `fvar#0 → Prop`".

const ITE_FIXTURE: &str = "\
axiom Pc : Prop
axiom Qc : Prop
axiom hpq : Pc = Qc
axiom dp : Decidable Pc
axiom A0 : Prop
axiom B0 : Prop
axiom hab : A0 = B0
";

/// `@ite Prop Pc dp A0 A0` with a condition rule that does NOT decide the
/// condition, so `try_simp_ite` declines and the spine is what protects the
/// `Decidable Pc` sibling. `hab` supplies the progress, so `simp only` does
/// not fail for want of a rewrite.
#[test]
fn test_simp_does_not_desync_an_ite_condition_from_its_decidable_instance() {
    assert_last_closed(
        &format!(
            "{ITE_FIXTURE}theorem t : @ite Prop Pc dp A0 A0 → True := by\n\
             \x20 intro h\n  simp only [hab, hpq] at h\n  trivial\n"
        ),
        "ite condition beside its Decidable sibling",
    );
}

/// `@Exists Pc E` — the implicit TYPE argument is frozen because the
/// predicate's type mentions it; `hE` rewrites the predicate, which is the
/// independent position.
#[test]
fn test_simp_does_not_desync_an_exists_type_from_its_predicate() {
    assert_last_closed(
        &format!(
            "{ITE_FIXTURE}axiom E : Pc → Prop\naxiom E2 : Pc → Prop\naxiom hE : E = E2\n\
             theorem t : (@Exists Pc E) → True := by\n\
             \x20 intro h\n  simp only [hpq, hE] at h\n  trivial\n"
        ),
        "Exists type argument beside its predicate",
    );
}

// ---------------------------------------------------------------------------
// `at *` gets the lemma list too
// ---------------------------------------------------------------------------
//
// Pinned v4.30.0-rc2:
//
// ```
// example (rule : A = B) (h : A) : B := by simp only [rule] at *; exact h
//   -- accepted
// example (rule : A = B) (h : A) : B := by simp only [] at *; exact h
//   -- error: `simp` made no progress
// ```
//
// Lean builds ONE `Simp.Context` in `mkSimpContext` and `simpLocation` hands
// it to every location. Clean's `Wildcard` arm called `simp_at_all` with no
// config, so the entire list — names, terms, `←`, `-`, `[*]` and `only` —
// was dropped for that one spelling, silently.

/// The goal is a DISJUNCTION throughout this section: Clean's simp runs an
/// assumption-shaped closer that would shut `⊢ B` from the rewritten `h : B`
/// and leave the trailing `exact` with no goals, so a bare goal cannot tell
/// "the list reached the wildcard" from "simp closed it anyway".
#[test]
fn test_simp_only_at_wildcard_uses_its_lemma_list() {
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (rule : A = B) (h : A) : B ∨ C := by\n\
             \x20 simp only [rule] at *\n  exact Or.inl h\n"
        ),
        "simp only [rule] at *",
    );
}

/// Control: the same spelling with an EMPTY list must not close, so the pass
/// above is attributable to the list reaching the wildcard path.
#[test]
fn test_simp_only_at_wildcard_with_an_empty_list_does_not_close() {
    assert_last_failed(
        &format!(
            "{RW_FIXTURE}theorem ctl (rule : A = B) (h : A) : B ∨ C := by\n\
             \x20 simp only [] at *\n  exact Or.inl h\n"
        ),
        "simp only [] at *",
    );
}

/// A `←` element at the wildcard, which only the resolved `prebuilt` channel
/// can carry.
#[test]
fn test_simp_reversed_argument_at_wildcard_reaches_the_hypotheses() {
    assert_last_closed(
        &format!(
            "{RW_FIXTURE}theorem t (rule : B = A) (h : A) : A ∨ C := by\n\
             \x20 simp only [← rule] at *\n  exact Or.inl h\n"
        ),
        "simp only [← rule] at *",
    );
}

// ---------------------------------------------------------------------------
// `thm` and `← thm` are ONE origin with opposite `inv`, and adding either
// ERASES the other — Lean's `eraseFwdIfBwd` / `Origin.converse`
// ---------------------------------------------------------------------------
//
// `Origin`'s own `BEq` compares `inv`
// (`Lean/Meta/Tactic/Simp/SimpTheorems.lean:93`, "we must distinguish `thm`
// from `←thm`"), so the two directions are distinct entries in one set — and
// Lean keeps them from ever coexisting: `addSimpTheorem` (:571) opens with
// `let d := eraseFwdIfBwd d e`, which erases the CONVERSE origin of what it
// is adding (issue #4290), and `SimpTheorems.erase` (:603) falls back to
// `thmId.converse` when the origin it was handed is not in the set.
//
// The consequence that matters is the SECOND test below: `simp [← r]` over a
// `@[simp]`-registered `r` is the ordinary Mathlib spelling, and without the
// erasure the registry's forward rule (priority 100) sits in the same set as
// this argument's reversed one (priority 50). The two oscillate and the
// forward one wins — so the reversed request loses to the exact rule it was
// written to override, silently. Measured before the fix: the goal came back
// `PP bb`, unmoved.
//
// Pinned v4.30.0-rc2 transcripts (`opaque a b : Nat`, `P : Nat → Prop`,
// `Q : Prop`; the goal is a DISJUNCTION for the reason the star section above
// gives — Clean's simp closes a bare `⊢ P a` from `h : P a` with no rewrite):
//
// ```text
// @[simp] axiom rabS : a = b
// example (h : P a) : P b ∨ Q := by simp; exact Or.inl h
//   -- error: `simp` made no progress
// example (h : P a) : P b ∨ Q := by simp [← rabS]; exact Or.inl h
//   -- accepted
//
// axiom rab : a = b                                        -- no @[simp]
// example (h : P a) : P b ∨ Q := by simp only [← rab]; exact Or.inl h
//   -- accepted
// example (h : P a) : P b ∨ Q := by simp only [rab, ← rab]; exact Or.inl h
//   -- accepted, plus `linter.unusedSimpArgs`: "This simp argument is unused: rab"
// example (h : P a) : P b ∨ Q := by simp only [← rab, rab]; exact Or.inl h
//   -- error: `simp` made no progress
// example (h : P a) : P b ∨ Q := by simp only [← rab, -rab]; exact Or.inl h
//   -- error: `simp` made no progress
// ```

const CONVERSE_FIXTURE: &str = "\
axiom PP : Nat → Prop
axiom QQ : Prop
axiom aa : Nat
axiom bb : Nat
";

/// Control: the `@[simp]`-registered FORWARD rule cannot touch `PP bb`, so
/// the pass below is attributable to the `←` element and nothing else.
#[test]
fn test_simp_registered_forward_rule_alone_does_not_close_the_reversed_goal() {
    assert_last_failed(
        &format!(
            "{CONVERSE_FIXTURE}@[simp] axiom rab : aa = bb\n\
             theorem ctl (h : PP aa) : PP bb ∨ QQ := by\n  simp\n  exact Or.inl h\n"
        ),
        "registered forward control",
    );
}

/// `simp [← rab]` with `rab` REGISTERED: the reversed element erases the
/// registry's forward rule, so `PP bb` reduces to `PP aa` and STAYS there.
#[test]
fn test_simp_reversed_argument_erases_the_registered_forward_rule() {
    assert_last_closed(
        &format!(
            "{CONVERSE_FIXTURE}@[simp] axiom rab : aa = bb\n\
             theorem t (h : PP aa) : PP bb ∨ QQ := by\n  simp [← rab]\n  exact Or.inl h\n"
        ),
        "simp [← rab] over a registered forward rule",
    );
}

/// Control for the three `simp only` shapes below: the reversed element alone
/// closes the goal.
#[test]
fn test_simp_only_reversed_argument_alone_closes_the_converse_goal() {
    assert_last_closed(
        &format!(
            "{CONVERSE_FIXTURE}axiom rab : aa = bb\n\
             theorem ctl (h : PP aa) : PP bb ∨ QQ := by\n\
             \x20 simp only [← rab]\n  exact Or.inl h\n"
        ),
        "simp only [← rab] control",
    );
}

/// `[rab, ← rab]`: the later reversed element erases the forward one, so the
/// list behaves exactly like `[← rab]`.
#[test]
fn test_simp_only_reverse_after_forward_erases_the_forward_rule() {
    assert_last_closed(
        &format!(
            "{CONVERSE_FIXTURE}axiom rab : aa = bb\n\
             theorem t (h : PP aa) : PP bb ∨ QQ := by\n\
             \x20 simp only [rab, ← rab]\n  exact Or.inl h\n"
        ),
        "simp only [rab, ← rab]",
    );
}

/// `[← rab, rab]`: the later FORWARD element erases the reversed one, so
/// nothing rewrites `PP bb` and the tactic must fail.
#[test]
fn test_simp_only_forward_after_reverse_erases_the_reversed_rule() {
    assert_last_failed(
        &format!(
            "{CONVERSE_FIXTURE}axiom rab : aa = bb\n\
             theorem t (h : PP aa) : PP bb ∨ QQ := by\n\
             \x20 simp only [← rab, rab]\n  exact Or.inl h\n"
        ),
        "simp only [← rab, rab]",
    );
}

/// `[← rab, -rab]`: `-` names the FORWARD origin, which is not in the set, so
/// Lean's `erase` falls back to the converse and removes the reversed rule
/// the previous element added.
#[test]
fn test_simp_only_erase_removes_the_reversed_rule_of_the_same_name() {
    assert_last_failed(
        &format!(
            "{CONVERSE_FIXTURE}axiom rab : aa = bb\n\
             theorem t (h : PP aa) : PP bb ∨ QQ := by\n\
             \x20 simp only [← rab, -rab]\n  exact Or.inl h\n"
        ),
        "simp only [← rab, -rab]",
    );
}

// ---------------------------------------------------------------------------
// OPEN, measured: `exclude_hypothesis` is wider than Lean's, and it has to be
// ---------------------------------------------------------------------------
//
// Lean's `simpGoal` erases the hypothesis it is about to simplify from its own
// set — but it erases the ORIGIN `.fvar fvarId`, and only the `[*]` channel
// registers a hypothesis under that origin (`applyStarArg` calls
// `addTheorem (.fvar h) ..`). An element that NAMES the hypothesis goes
// through `elabDeclToUnfoldOrTheorem`'s fvar arm, which keeps the `.stx`
// origin `elabSimpArg` minted for it (`Lean/Elab/Tactic/Simp.lean:261,187`),
// and `.stx` never equals `.fvar` — so in Lean the NAMED rule survives and the
// hypothesis is rewritten by itself. `SimpConfig::exclude_hypothesis` is read
// by `collect_extra_lemmas` as well, so Clean refuses that spelling.
//
// Pinned v4.30.0-rc2:
//
// ```text
// axiom P : Prop
// example (h : P) : True := by simp only [h] at h; trivial
//   -- accepted (only a `linter.unusedVariables` warning for `h`)
// example (h : P) : True := by simp only [*] at h; trivial
//   -- error: `simp` made no progress
// ```
//
// DO NOT close this by dropping the `collect_extra_lemmas` read — that was
// tried and MEASURED, and it breaks a shape Lean also accepts:
//
// ```text
// example (rule : A = B) (h : A) : B ∨ C := by simp only [rule] at *
//                                              exact Or.inl h   -- accepted
// example (rule : A = B) : True := by simp only [rule] at rule; trivial
//                                                              -- accepted
// ```
//
// Lean gets BOTH because `mkSimpContext` builds ONE `Simp.Context` from the
// ORIGINAL context and `simpLocation` hands the same set to every location,
// while Clean rebuilds the lemma set per hypothesis from the MUTATED goal
// (`simp_hyps` / `simp_at_all_with_config` call `simp_at_with_config`, which
// re-collects). Without the exclusion, `rule` is rewritten to `True` at its
// own location first and is no longer an equation when `h` is reached, so
// `test_simp_only_at_wildcard_uses_its_lemma_list` above went red. The
// Lean-faithful fix is to collect ONCE and pass the set to every location
// (`simp_at_with_lemmas`, which `simp_all_with_config` already does) — and
// that has its own hazard, because a rule's proof names a hypothesis fvar
// that an earlier location may already have replaced. Separate work; pinned
// here as a refusal so it fails loudly the day it closes.

/// The NAMED channel is excluded too, which Lean does not do. `expect_err`
/// plus the target assertion: when this starts passing, delete the refusal and
/// assert the close.
#[test]
fn test_simp_at_a_hypothesis_refuses_the_named_rule_for_that_hypothesis() {
    assert_last_failed(
        "axiom P : Prop\n\
         theorem t (h : P) : True := by\n  simp only [h] at h\n  trivial\n",
        "simp only [h] at h (OPEN: pinned Lean accepts this)",
    );
}

/// The star channel IS excluded, which is the half `simpGoal` really does —
/// the control that tells the two channels apart, and the half that must not
/// change when the refusal above closes.
#[test]
fn test_simp_at_a_hypothesis_does_not_use_the_star_rule_of_that_hypothesis() {
    assert_last_failed(
        "axiom P : Prop\n\
         theorem t (h : P) : True := by\n  simp only [*] at h\n  trivial\n",
        "simp only [*] at h",
    );
}

// ---------------------------------------------------------------------------
// The term path's own near misses: a hole the pattern DOES determine, and the
// `@`-explicit head
// ---------------------------------------------------------------------------
//
// `abstract_open_metas` is Lean's `abstractMVars`: a metavariable elaboration
// leaves open becomes a PATTERN variable, not a side goal. The question that
// makes it adversarial is whether the resulting rule matches more than Lean's
// would — so each shape below is pinned at the exact index it must fire at,
// with the wrong index beside it.
//
// Pinned v4.30.0-rc2:
//
// ```text
// axiom f : Nat → Prop
// axiom g : Nat → Prop
// axiom ruleN : (n : Nat) → f n = g n
// axiom hg : g 7
// example : f 7 := by simp only [ruleN _];   exact hg   -- accepted
// example : f 7 := by simp only [@ruleN];    exact hg   -- accepted
// example : f 7 := by simp only [@ruleN 7];  exact hg   -- accepted
// example : f 7 := by simp only [@ruleN 8];  exact hg   -- `simp` made no progress
// ```

const TERM_ARG_FIXTURE: &str = "\
axiom f : Nat → Prop
axiom g : Nat → Prop
axiom ruleN : (n : Nat) → f n = g n
axiom hg : g 7
";

/// A hole the LHS determines: `?n` is abstracted to a pattern variable and
/// the match binds it, so no goal is gained and the rewrite fires.
#[test]
fn test_simp_only_term_argument_hole_the_pattern_determines_rewrites() {
    assert_last_closed(
        &format!("{TERM_ARG_FIXTURE}theorem t : f 7 := by\n  simp only [ruleN _]\n  exact hg\n"),
        "simp only [ruleN _]",
    );
}

/// The `@`-explicit head with no arguments: `rw_rule_is_name` refuses
/// `Explicit`, so this is the term path even though it spells one name.
#[test]
fn test_simp_only_explicit_head_with_no_arguments_rewrites() {
    assert_last_closed(
        &format!("{TERM_ARG_FIXTURE}theorem t : f 7 := by\n  simp only [@ruleN]\n  exact hg\n"),
        "simp only [@ruleN]",
    );
}

/// The `@`-explicit head applied at the index the goal uses.
#[test]
fn test_simp_only_explicit_application_at_the_matching_index_rewrites() {
    assert_last_closed(
        &format!("{TERM_ARG_FIXTURE}theorem t : f 7 := by\n  simp only [@ruleN 7]\n  exact hg\n"),
        "simp only [@ruleN 7]",
    );
}

/// The near miss that says the abstraction did not widen the rule: the SAME
/// lemma pinned at another index must not fire at `f 7`.
#[test]
fn test_simp_only_explicit_application_at_the_wrong_index_does_not_rewrite() {
    assert_last_failed(
        &format!("{TERM_ARG_FIXTURE}theorem t : f 7 := by\n  simp only [@ruleN 8]\n  exact hg\n"),
        "simp only [@ruleN 8]",
    );
}

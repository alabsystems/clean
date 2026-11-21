// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The TACTIC forms of the battery: `cases h : e`, `match h : e`, an
//! alternative's own column, `case some.cons`, the `↓`/`↑` simp markers,
//! `solve`, and several alternative left-hand sides.

use crate::common::*;

// --- `cases h : e` -------------------------------------------------------

#[test]
fn test_cases_named_target_branch_equation_names_the_constructor() {
    // `h : f n = none` in the `none` branch is exactly what `absurd h hn`
    // needs; the target's `f n` is generalized, so `rfl` closes `some y =
    // some y` in the other branch. An older hypothesis spelled `h` must not
    // be the one reverted.
    let src = format!(
        "{OPT_FN}theorem cases_eq (n : Nat) (h : True) (hn : f n ≠ none) : \
         ∃ y, f n = some y := by\n  cases h : f n with\n  | none => exact absurd h hn\n  \
         | some y => exact ⟨y, rfl⟩\n"
    );
    expect_axiom_free(&src, "`cases h : f n with`", &["cases_eq"]);
}

#[test]
fn test_cases_named_target_without_alternatives_reintroduces_equation() {
    let src = format!(
        "{OPT_FN}theorem cases_eq_bullets (n : Nat) (hn : f n ≠ none) : \
         ∃ y, f n = some y := by\n  cases h : f n\n  · exact absurd h hn\n  \
         · exact ⟨_, rfl⟩\n"
    );
    expect_axiom_free(&src, "`cases h : f n` with bullets", &["cases_eq_bullets"]);
}

#[test]
fn test_cases_named_target_equation_is_not_the_generalized_target() {
    // Lean 4.8: "application type mismatch … h has type f n = some y but is
    // expected to have type some y = some y" — `h` keeps the ORIGINAL term.
    let src = format!(
        "{OPT_FN}theorem cases_eq_twin (n : Nat) (hn : f n ≠ none) : \
         ∃ y, f n = some y := by\n  cases h : f n with\n  | none => exact absurd h hn\n  \
         | some y => exact ⟨y, h⟩\n"
    );
    expect_refused_at(
        &src,
        "`h` used as the generalized equation",
        "cases_eq_twin",
        MISMATCH,
    );
}

#[test]
fn test_cases_named_target_some_branch_equation_names_its_field() {
    let src = format!(
        "{OPT_FN}theorem cases_eq_some (n : Nat) (hn : ∀ y, f n ≠ some y) : f n = none := by\n  \
         cases h : f n with\n  | none => rfl\n  | some y => exact absurd h (hn y)\n"
    );
    expect_axiom_free(
        &src,
        "`h : f n = some y` in the `some y` branch",
        &["cases_eq_some"],
    );
}

#[test]
fn test_cases_named_target_equation_is_branch_specific() {
    // In the `none` branch `h : f n = none`, never `f n = some _`.
    let src = format!(
        "{OPT_FN}theorem cases_eq_wrong_branch (n : Nat) (hn : ∀ y, f n ≠ some y) : f n = none := by\n  \
         cases h : f n with\n  | none => exact absurd h (hn 0)\n  | some y => exact absurd h (hn y)\n"
    );
    expect_refused_at(
        &src,
        "a `none`-branch equation used as a `some` one",
        "cases_eq_wrong_branch",
        MISMATCH,
    );
}

// --- tactic `match h : e with` -------------------------------------------

const MATCH_G: &str = "def g (xs : List Nat) : List Nat := xs.reverse\n\n";

#[test]
fn test_tactic_match_annotated_discriminant_binds_the_arm_equation() {
    let src = format!(
        "{MATCH_G}theorem match_h (xs : List Nat) (h0 : g xs ≠ []) : ∃ y ys, g xs = y :: ys := by\n  \
         match hxs : g xs with\n  | [] => exact absurd hxs h0\n  | y :: ys => exact ⟨y, ys, rfl⟩\n"
    );
    expect_axiom_free(&src, "tactic `match hxs : g xs with`", &["match_h"]);
}

#[test]
fn test_tactic_match_annotated_discriminant_is_not_the_generalized_target() {
    // Lean 4.8: "hxs has type g xs = y :: ys but is expected to have type
    // y :: ys = y :: ys" — the goal's `g xs` was generalized, `hxs` was not.
    let src = format!(
        "{MATCH_G}theorem match_h_twin (xs : List Nat) (h0 : g xs ≠ []) : ∃ y ys, g xs = y :: ys := by\n  \
         match hxs : g xs with\n  | [] => exact absurd hxs h0\n  | y :: ys => exact ⟨y, ys, hxs⟩\n"
    );
    expect_refused_at(
        &src,
        "`hxs` used as the generalized equation",
        "match_h_twin",
        MISMATCH,
    );
}

// --- an alternative's own column -----------------------------------------

#[test]
fn test_alternative_body_sibling_cases_after_term_tactic_elaborates() {
    let src = "theorem alt_col (n : Nat) (m : Nat → Option Nat) : n = n := by\n  \
               induction n with\n  | zero => rfl\n  | succ k ih =>\n    \
               have hk : k = k := rfl\n    cases m k with\n    | none => rfl\n    \
               | some b => rfl\n";
    expect_axiom_free(
        src,
        "a `cases` after a term tactic in an alternative",
        &["alt_col"],
    );
}

#[test]
fn test_alternative_body_deeper_line_is_an_argument_and_is_rejected() {
    // A line indented PAST the alternative's first tactic continues that
    // tactic's term (`checkColGt`): Lean reads `exact rfl cases m k` and fails.
    let src = "theorem alt_col_twin (n : Nat) (m : Nat → Option Nat) : n = n := by\n  \
               induction n with\n  | zero => rfl\n  | succ k ih =>\n    exact rfl\n      \
               cases m k with\n      | none => rfl\n      | some b => rfl\n";
    // The refusal is a parse failure (`with` after a term), reported for the
    // twin's own declaration or as the parser-recovery placeholder that
    // replaced it — the source holds no other declaration.
    let err = expect_refused(src, "a deeper line read as a sibling tactic");
    assert!(
        err.starts_with("alt_col_twin: ")
            || (err.starts_with('<') && err.to_lowercase().contains("parse")),
        "the refusal must be the twin's own: {err}"
    );
}

// --- `case some.cons` ----------------------------------------------------

#[test]
fn test_case_dotted_tag_selects_the_nested_goal_and_names_its_fields() {
    // `hd : Nat` and `tl : List Nat` are the `cons` fields under `some`; the
    // `show` only type-checks with those names on those fields.
    let src = "theorem case_dotted (o : Option Bool) (l : List Nat) : l.length = l.length := by\n  \
               cases o <;> cases l\n  case some.cons hd tl => show (hd :: tl).length = (hd :: tl).length; rfl\n  \
               all_goals rfl\n";
    expect_axiom_free(src, "`case some.cons hd tl`", &["case_dotted"]);
}

#[test]
fn test_case_dotted_tag_in_wrong_order_is_rejected() {
    // Lean 4.8: "Case tag 'cons.some' not found."
    let src =
        "theorem case_dotted_twin (o : Option Bool) (l : List Nat) : l.length = l.length := by\n  \
               cases o <;> cases l\n  case cons.some => rfl\n  all_goals rfl\n";
    expect_refused_at(src, "`case cons.some`", "case_dotted_twin", &["cons.some"]);
}

// --- `↓` / `↑` simp markers ----------------------------------------------

/// `(if False then a else b) = b`, the goal the simproc rows share: closed by
/// `reduceIte` and by nothing else a `simp only` list names here.
const ITE_FALSE: &str = "(a b : Nat) : (if False then a else b) = b := by\n  simp only ";

#[test]
fn simp_applied_lemma_instantiates_its_universe_at_each_match() {
    let accepted = r#"
theorem appliedIfMixed {T : Type u} (p : Prop) [Decidable p] (yes : p)
    (x y : Nat) (a b : T) :
    ((if p then x else y), (if p then a else b)) = (x, a) := by
  simp only [if_pos yes]
"#;
    expect_axiom_free(
        accepted,
        "one simp proof at two universes",
        &["appliedIfMixed"],
    );

    let refused = r#"
theorem appliedIfWrong (p q : Prop) [Decidable p] (yes : q) (x y : Nat) :
    (if p then x else y) = x := by
  simp only [if_pos yes]
"#;
    expect_refused_at(
        refused,
        "a proof of the wrong condition",
        "appliedIfWrong",
        &[],
    );
}

#[test]
fn bare_proof_infers_the_written_family_argument() {
    let source = r"
def Written (A : Type u) : Prop := True
theorem writtenWitness {A : Type u} : Written A := True.intro
theorem bareWrittenWitness (A : Type u) : Written A := writtenWitness
";
    expect_axiom_free(
        source,
        "bare proof at a written family",
        &["bareWrittenWitness"],
    );
}

#[test]
fn test_simp_only_naming_reduce_ite_runs_it() {
    // `reduceIte` is a Lean 4.8.0 builtin simproc: it resolves with no
    // constant in the environment, marked or not, and under `simp only`
    // naming it is what makes it run (pinned Lean closes all four). The
    // `ite` collapse is Clean's implementation of it; the conditional row
    // collapses a rewritten condition, the others one that is ALREADY
    // `False`, which only a `reduceIte` scope does.
    let src = format!(
        "theorem simp_pre {ITE_FALSE}[↓reduceIte]\n\n\
         theorem simp_post {ITE_FALSE}[↑reduceIte]\n\n\
         theorem simp_plain {ITE_FALSE}[reduceIte]\n\n\
         theorem simp_erase_then_add {ITE_FALSE}[-reduceIte, ↓reduceIte]\n\n\
         theorem simp_cond (a b : Nat) (c : Prop) [Decidable c] (h : c = False) : \
         (if c then a else b) = b := by\n  simp only [h, ↓reduceIte]\n"
    );
    expect_axiom_free(
        &src,
        "a named `reduceIte`",
        &[
            "simp_pre",
            "simp_post",
            "simp_plain",
            "simp_erase_then_add",
            "simp_cond",
        ],
    );
}

#[test]
fn test_simp_only_reduce_ite_condition_decided_by_constructor_equality() {
    // `reduceIte` simps the condition with Lean's always-on steps: an
    // equation between DIFFERENT constructors is `False` (`simpCtorEq`), and
    // `t = t` is `True` (`eq_self`, a `simp only` builtin). Pinned Lean 4.8.0
    // accepts all four; trust-ir's `simp only [bne_self_eq_false,
    // ↓reduceIte]` reaches the first shape. (`simpCtorEq` is not injection:
    // `ctor_eq.rs`' unit tests pin `some 1 = some 2` as left alone.)
    let src = "inductive Color where\n  | red\n  | green\n  deriving DecidableEq\n\n\
               theorem ctor_bool (x y : Nat) : (if false = true then x else y) = y := by\n  \
               simp only [↓reduceIte]\n\n\
               theorem ctor_color (x y : Nat) : (if Color.red = Color.green then x else y) = y := by\n  \
               simp only [↓reduceIte]\n\n\
               theorem ctor_nat (x y : Nat) : (if (0 : Nat) = 1 then x else y) = y := by\n  \
               simp only [↓reduceIte]\n\n\
               theorem ctor_self (x y : Nat) : (if true = true then x else y) = x := by\n  \
               simp only [↓reduceIte]\n";
    expect_axiom_free(
        src,
        "`reduceIte` over a constructor equation",
        &["ctor_bool", "ctor_color", "ctor_nat", "ctor_self"],
    );
}

/// An `ite` whose condition only a hypothesis decides, so neither the
/// kernel's `ite` evaluation (no closed instance) nor any lemma but `h`
/// touches it: whether it collapses is exactly whether `reduceIte` runs.
const ITE_BY_HYP: &str = "(a b : Nat) (c : Prop) [Decidable c] (h : c = False) : \
                          (if c then a else b) = b := by\n  simp only ";

#[test]
fn test_simp_only_naming_another_simproc_does_not_run_reduce_ite() {
    // Pinned Lean 4.8.0 refuses both ("unsolved goals ⊢ (if False then a
    // else b) = b": `h` rewrites the condition and nothing collapses the
    // `ite`). A `simp only` list that names simprocs runs exactly those:
    // `reduceDite` is not `reduceIte`, and a `-reduceIte` after `↓reduceIte`
    // erases it. Clean, which does not rewrite a condition its `Decidable`
    // instance depends on, refuses with "no progress". With the named
    // simproc skipped, Clean's whole simproc set ran and the `ite` collapse
    // closed both.
    for (decl, list) in [
        ("simp_dite_on_ite", "[h, ↓reduceDite]"),
        ("simp_add_then_erase", "[h, ↓reduceIte, -reduceIte]"),
    ] {
        let src = format!("theorem {decl} {ITE_BY_HYP}{list}\n");
        expect_refused_at(&src, list, decl, NO_PROGRESS);
    }
}

#[test]
fn test_simp_only_unimplemented_simproc_is_refused_by_name() {
    // PINNED GAP. Clean implements `reduceIte`/`reduceDite` only, and its own
    // `Nat.reduceAdd` (nested evaluation, more heads) is not Lean's, so a
    // `simp only` naming `Nat.reduceAdd` is refused by name — never accepted
    // and skipped. Pinned Lean 4.8.0 refuses the `ite` goal too ("simp made
    // no progress") but ACCEPTS `2 + 2 = 4` by `simp only [↓Nat.reduceAdd]`;
    // the day Clean implements it, the second row flips.
    for (decl, src) in [
        (
            "simp_nat_pre",
            format!("theorem simp_nat_pre {ITE_FALSE}[↓Nat.reduceAdd]\n"),
        ),
        (
            "simp_nat_plain",
            format!("theorem simp_nat_plain {ITE_FALSE}[Nat.reduceAdd]\n"),
        ),
        (
            "simp_nat_lean_accepts",
            "theorem simp_nat_lean_accepts : 2 + 2 = 4 := by\n  simp only [↓Nat.reduceAdd]\n"
                .to_string(),
        ),
    ] {
        let err = expect_refused_at(&src, decl, decl, &["not implemented by Clean"]);
        assert!(
            err.contains("`Nat.reduceAdd`"),
            "the refusal must name the simproc: {err}"
        );
    }
}

#[test]
fn test_simp_default_set_simproc_changes_are_refused_by_name() {
    // PINNED GAP. Pinned Lean 4.8.0 accepts both: `-reduceIte` drops the
    // simproc from the default set (`ite_true` still closes the goal), and
    // `Nat.isValue` — registered for `seval` only — joins it. Clean's default
    // simp set cannot mirror either change (its `ite` collapse and simproc
    // table stand in for Lean's set), so it refuses them by name rather than
    // ignore them. Naming a simproc the default set already holds is the
    // no-op it is in Lean (`simp [↓reduceIte]`).
    let goal = "(a b : Nat) : (if True then a else b) = a := by\n  simp ";
    for (decl, list, reason) in [
        (
            "simp_erase_default",
            "[-reduceIte]",
            "erasing simproc `reduceIte`",
        ),
        ("simp_seval_only", "[Nat.isValue]", "simproc `Nat.isValue`"),
    ] {
        let src = format!("theorem {decl} {goal}{list}\n");
        expect_refused_at(&src, list, decl, &[reason]);
    }
    let src = format!("theorem simp_default_named {goal}[↓reduceIte]\n");
    expect_axiom_free(
        &src,
        "a default-set simproc named in plain `simp`",
        &["simp_default_named"],
    );
}

#[test]
fn test_simp_only_naming_no_simproc_runs_none() {
    // Lean 4.8.0's `simp only` with no simproc named runs none (pinned Lean:
    // "unsolved goals ⊢ (if False then a else b) = b"). Clean used to keep
    // its whole simproc set there (`SimprocScope::CleanBuiltins`), whose
    // `ite` collapse closed it — a pinned over-acceptance until review r4t,
    // when `simp only` with nothing named got Lean's empty set. Clean, which
    // does not rewrite a condition its `Decidable` instance depends on,
    // refuses with "no progress".
    let src = format!("theorem simp_no_simproc {ITE_BY_HYP}[h]\n");
    expect_refused_at(
        &src,
        "`simp only [h]` on an `ite` over `c`",
        "simp_no_simproc",
        NO_PROGRESS,
    );
}

#[test]
fn test_simp_no_progress_closer_decides_a_closed_ite() {
    // PINNED DIVERGENCE (over-acceptance), in every simproc scope. When simp
    // makes no progress Clean still tries `close_refl_reducible`, whose
    // reducible-transparency def-eq check runs the kernel's NATIVE `ite` /
    // `decEq` reducers, which ignore transparency: a goal `ite C a b = b`
    // with a CLOSED decidable condition closes by evaluation. Pinned Lean
    // 4.8.0 answers each of these "simp made no progress" (its `eq_self`
    // does not unfold `ite`). Fixing it means native reducers honouring the
    // transparency of the query (`clean-kernel` `tc/def_eq/delta_helpers.rs`
    // `reduce_native`).
    let src = format!(
        "inductive Box where\n  | mk : Nat → Box\n  deriving DecidableEq\n\n\
         theorem close_lit {ITE_FALSE}[↓reduceDite]\n\n\
         theorem close_nat (a b : Nat) : (if 2 = 3 then a else b) = b := by\n  simp only [↓reduceIte]\n\n\
         theorem close_box (a b : Nat) : (if Box.mk 1 = Box.mk 2 then a else b) = b := by\n  \
         simp only [↓reduceIte]\n"
    );
    expect_accepted(&src, "a closed `ite` the no-progress closer evaluates");
}

#[test]
fn test_simp_marked_theorem_and_local_are_ordinary_rules() {
    let src =
        "theorem simp_marked_thm (a : Nat) : a + 0 = a := by\n  simp only [↓Nat.add_zero]\n\n\
               theorem simp_marked_local (a b : Nat) (h : a = b) : a + 0 = b := by\n  \
               simp only [↑h, Nat.add_zero]\n";
    expect_axiom_free(
        src,
        "a marked theorem and a marked local",
        &["simp_marked_thm", "simp_marked_local"],
    );
}

#[test]
fn test_simp_pre_marker_does_not_prove_a_false_goal() {
    // Lean 4.8 leaves `a = b` unsolved.
    let src = "theorem simp_pre_twin (a b : Nat) : (if True then a else b) = b := by\n  \
               simp only [↓reduceIte]\n";
    expect_refused_at(
        src,
        "`↓reduceIte` on a goal it cannot close",
        "simp_pre_twin",
        &[],
    );
}

#[test]
fn test_simp_marked_rule_naming_nothing_is_refused_by_name() {
    // Lean 4.8: "unknown identifier 'no_such_rule_xyz'" — even though
    // `↓reduceIte` alone closes the goal.
    let src = "theorem simp_bogus (a b : Nat) : (if False then a else b) = b := by\n  \
               simp only [↓reduceIte, ↓no_such_rule_xyz]\n";
    let err = expect_refused_at(
        src,
        "`↓no_such_rule_xyz`",
        "simp_bogus",
        &["unknown identifier"],
    );
    assert!(
        err.contains("no_such_rule_xyz"),
        "the refusal must name the rule: {err}"
    );
}

// --- `solve` -------------------------------------------------------------

#[test]
fn test_solve_takes_the_alternative_that_closes_the_goal() {
    let src = "theorem solve_ok (p q : Prop) (hq : q) : p ∨ q := by\n  solve\n  \
               | exact Or.inl hq\n  | exact Or.inr hq\n";
    expect_axiom_free(src, "`solve | … | …`", &["solve_ok"]);
}

#[test]
fn test_solve_refuses_alternatives_that_leave_goals() {
    // Lean 4.8: every alternative leaves a goal, so `done` fails each one.
    let src = "theorem solve_bad (p q : Prop) (hq : q) : p ∨ q := by\n  solve\n  \
               | apply Or.inr\n  | apply Or.inl\n";
    expect_refused_at(
        src,
        "`solve` whose alternatives do not close the goal",
        "solve_bad",
        &[],
    );
}

// --- several left-hand sides ---------------------------------------------

const OP_TOTAL: &str = "inductive Op where\n  | add | sub | mul | div\n\n\
                        def Op.total : Op → Bool\n  | .div => false\n  | _ => true\n\n";

#[test]
fn test_alternative_with_several_lhs_runs_its_tactics_for_each() {
    let src = format!(
        "{OP_TOTAL}theorem total_or (o : Op) : o.total = true ∨ o = .div := by\n  cases o with\n  \
         | add | sub | mul => exact Or.inl rfl\n  | div => exact Or.inr rfl\n"
    );
    expect_axiom_free(&src, "`| add | sub | mul => …`", &["total_or"]);
}

#[test]
fn test_alternative_with_several_lhs_does_not_cover_a_false_case() {
    let src = format!(
        "{OP_TOTAL}theorem total_twin (o : Op) : o.total = true ∨ o = .div := by\n  cases o with\n  \
         | add | sub | div => exact Or.inl rfl\n  | mul => exact Or.inr rfl\n"
    );
    expect_refused_at(
        &src,
        "a shared alternative over a constructor it does not prove",
        "total_twin",
        MISMATCH,
    );
}

#[test]
fn test_alternative_binder_spelled_like_a_tactic_binds_the_field() {
    let src = "theorem alt_lhs (i : Nat × Nat) : i.1 = i.1 := by\n  cases i with\n  \
               | mk lhs rhs => show lhs = lhs; rfl\n";
    expect_axiom_free(src, "`| mk lhs rhs`", &["alt_lhs"]);
}

#[test]
fn constructor_tries_the_next_constructor_when_indices_do_not_unify() {
    let source = "inductive Mark : Nat → Prop where\n  \
        | base : Mark 0\n  | step (n : Nat) : Mark n → Mark (Nat.succ n)\n\n\
        theorem markTwo : Mark 2 := by repeat' constructor\n";
    let env = expect_accepted(source, "reach the later matching indexed constructor");
    assert_no_axioms(&env, "markTwo");
}

#[test]
fn constructor_refuses_an_impossible_index_and_keeps_the_first_applicable_branch() {
    let source = "inductive Select : Nat → Prop where\n  \
        | first : False → Select 0\n  | second : Select 0\n";
    for (index, reason) in [(1, "no applicable constructor"), (0, "unsolved goal")] {
        expect_refused_at(
            &format!("{source}theorem choose : Select {index} := by constructor\n"),
            "constructor tries candidates only until application succeeds",
            "choose",
            &[reason],
        );
    }
}

#[test]
fn constructor_rolls_back_a_witness_from_an_inapplicable_indexed_constructor() {
    let source = r#"
inductive Probe : Nat → Nat → Prop where
  | first : Probe 0 0
  | second : Probe 1 1

theorem existsOne : ∃ n, Probe n 1 := by
  apply Exists.intro
  constructor
"#;
    let env = expect_accepted(source, "the second candidate can assign the witness to one");
    assert_no_axioms(&env, "existsOne");
}

#[test]
fn change_holes_follow_the_focused_goal_and_refuse_a_crossed_local_bound() {
    // Pinned Lean accepts these three proofs and refuses the crossed change.
    let source = r#"
theorem changeBound : True ∧ ((0 : Nat) < 1 ∧ True) :=
  ⟨True.intro, ⟨by change (_ : Nat) < _; decide, True.intro⟩⟩
theorem changeLocal (n m : Nat) (h : n < m) : True ∧ n < m :=
  ⟨True.intro, by change (_ : Nat) < _; exact h⟩
theorem changeRollback (n m : Nat) (h : n < m) : n < m := by
  first | change (_ : Nat) < n | change (_ : Nat) < _
  exact h
"#;
    expect_axiom_free(
        source,
        "focused change with placeholders",
        &["changeBound", "changeLocal", "changeRollback"],
    );
    expect_refused_at(
        "theorem changeWrong (n m : Nat) (h : n < m) : n < m := by\n  change (_ : Nat) < n\n  exact h",
        "change with crossed rigid upper bound",
        "changeWrong",
        &["change: new type is not definitionally equal"],
    );
}

#[test]
fn change_rechecks_hypotheses_and_their_dependents() {
    let accepted = r#"
theorem changeHyp (n m : Nat) (h : n < m) (proof : h = h) : h = h := by
  change (_ : Nat) < _ at h
  exact proof
theorem changeMany (n m p : Nat) (h : n < m) (k : m < p) : n < m ∧ m < p := by
  change (_ : Nat) < _ at h k
  exact ⟨h, k⟩
theorem changeAll (n m : Nat) (h : n < m) : True ∧ n < m := by
  change (_ : Nat) < _ at *
  exact ⟨True.intro, h⟩
theorem changeRight (p : Nat → Prop) (h : p (1 + 1)) : p 2 := by
  have right := h
  have checked : p 2 := by
    change p 2 at right
    exact right
  exact checked
"#;
    expect_axiom_free(
        accepted,
        "change at checked hypothesis locations",
        &["changeHyp", "changeMany", "changeAll", "changeRight"],
    );
    expect_refused_at(
        "theorem changeBadHyp (n m : Nat) (h : n < m) : True := by\n  change n = m at h\n  exact True.intro",
        "change at an incompatible hypothesis",
        "changeBadHyp",
        &["not definitionally equal to hypothesis"],
    );
}

#[test]
fn constructor_named_args_use_the_checked_source_telescope() {
    let declaration = "inductive NamedTyping (policy : Nat → Prop) : Nat → Prop where\n\
        | constant {Γ argument : Nat} (equality : argument = Γ) : NamedTyping policy Γ\n";
    let theorem = "theorem originalConstructor {policy : Nat → Prop} : NamedTyping policy 2 :=\n\
        NamedTyping.constant (argument := 2) (Γ := 2) rfl\n";
    let combined = format!("{declaration}{theorem}");
    expect_axiom_free(
        &combined,
        "named source constructor",
        &["originalConstructor"],
    );
    let wrong_value = combined.replace("argument := 2", "argument := 1");
    expect_refused_at(
        &wrong_value,
        "wrong source constructor endpoint",
        "originalConstructor",
        &[],
    );
    let wrong_name = combined.replace("argument := 2", "missing := 2");
    expect_refused_at(
        &wrong_name,
        "unknown source constructor binder",
        "originalConstructor",
        &[],
    );
}

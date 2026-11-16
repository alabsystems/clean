// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Second adversarial battery for simp's lemma construction: WHICH constants
//! and hypotheses become rules, and which binder types are instance slots.
//!
//! Every fixture is the EXACT text that was run on the pinned v4.30.0-rc2
//! `lean` binary (2026-09-20): each declaration named in a `refused` list
//! fails there ("`simp` made no progress", or "Type mismatch: After
//! simplification" for `sa_mismatch`) and every other one elaborates as
//! written. Six groups were RED on the package as reviewed and are the
//! repairs that landed with this file:
//!
//! * a constant is a simp THEOREM when its TYPE is a proposition (Lean's
//!   `addDeclToUnfoldOrTheorem`), whatever kind of constant it is — a
//!   constructor of an inductive proposition, a proposition-valued structure
//!   or class field, a `def` of a proposition; every `Definition`-kind
//!   constant was dropped;
//! * an instance slot is any binder whose type's `∀` telescope ENDS in a
//!   class, through reducible aliases (Lean's `isClass?`) —
//!   `[∀ n, Decidable (p n)]` was never synthesized, not even from a local;
//! * a `@[simp]` lemma is not shadowed by a hypothesis that shares its NAME;
//!   read as a local rule it lost its level renaming and a
//!   universe-polymorphic `↔` lemma was refused;
//! * a CONDITIONAL rule made of a local hypothesis (`ih : ∀ m, m < n → …`)
//!   has its premise discharged like a global lemma's; every such rule was
//!   refused;
//! * `simpa … using e` with `e` simplified to `False` closes the goal;
//! * a LOCAL conjunction is split into its conjuncts' rules, as a global one
//!   already was.
//!
//! One measured divergence is PINNED as a refusal rather than repaired
//! ([`test_simp_conjunct_under_its_own_forall_is_not_opened_yet`]).

use crate::tests_simp_lemma_adversarial::{assert_refused_exactly, failures};

const SOURCES: &str = r#"axiom PP : Nat → Prop
axiom pp3 : PP 3
class Refl2 (r : Nat → Nat → Prop) : Prop where
  refl : ∀ a, r a a
theorem src_class_field (r : Nat → Nat → Prop) [Refl2 r] (k : Nat) : r k k := by
  simp only [Refl2.refl]
structure Pack where
  val : Nat
  ok : PP val
theorem src_struct_field (s : Pack) : PP s.val := by simp only [Pack.ok]
def myproof : PP 3 := pp3
theorem src_def_prop : PP 3 := by simp only [myproof]
inductive Ev : Nat → Prop where
  | zero : Ev 0
  | step (n : Nat) : Ev n → Ev (n + 2)
theorem src_ctor : Ev 0 := by simp only [Ev.zero]
theorem src_ctor_cond (n : Nat) (h : Ev n) : Ev (n + 2) := by simp only [Ev.step, h]
theorem src_ctor_near : Ev 1 := by simp only [Ev.zero]
def notProp (n : Nat) : Prop := PP n
theorem src_def_unfolds : notProp 3 := by simp only [notProp, pp3]
theorem src_def_not_a_theorem : notProp 3 := by simp only [pp3]
attribute [simp] Ev.zero
theorem src_ctor_registry : Ev 0 ∧ True := by simp
"#;

/// Lean decides "theorem or definition to unfold" by `isProp info.type`
/// alone. A class field (`src_class_field`), a structure field
/// (`src_struct_field`), a `def` of a proposition (`src_def_prop`) and the
/// constructors of an inductive proposition — unconditional, conditional,
/// and through the `@[simp]` registry (`src_ctor*`) — are all rules. The
/// near misses: `Ev.zero` says nothing about `Ev 1`, and a `def` whose type is
/// `Nat → Prop` is NOT a theorem — it is unfolded when named
/// (`src_def_unfolds`) and opaque when not (`src_def_not_a_theorem`).
#[test]
fn test_simp_theorem_is_decided_by_the_type_not_the_constant_kind() {
    assert_refused_exactly(
        SOURCES,
        &[
            ("src_ctor_near", "NoProgress"),
            ("src_def_not_a_theorem", "NoProgress"),
        ],
    );
}

const PI_SLOTS: &str = r#"axiom QQ : Prop → Prop
axiom RR : Nat → Prop
axiom decRR (n : Nat) : Decidable (RR n)
noncomputable instance instRR (n : Nat) : Decidable (RR n) := decRR n
axiom lemPi (p : Nat → Prop) [∀ n, Decidable (p n)] : QQ (∀ n, p n) ↔ True
theorem pi_local (p : Nat → Prop) [∀ n, Decidable (p n)] : QQ (∀ n, p n) := by
  simp only [lemPi]
theorem pi_global : QQ (∀ n, RR n) := by simp only [lemPi]
theorem pi_none (p : Nat → Prop) : QQ (∀ n, p n) := by simp only [lemPi]
abbrev DecAll (p : Nat → Prop) := ∀ n, Decidable (p n)
axiom lemAlias (p : Nat → Prop) [DecAll p] : QQ (∀ n, p n) ↔ True
theorem alias_local (p : Nat → Prop) [DecAll p] : QQ (∀ n, p n) := by simp only [lemAlias]
theorem alias_from_pi (p : Nat → Prop) [∀ n, Decidable (p n)] : QQ (∀ n, p n) := by
  simp only [lemAlias]
theorem alias_global : QQ (∀ n, RR n) := by simp only [lemAlias]
theorem alias_none (p : Nat → Prop) : QQ (∀ n, p n) := by simp only [lemAlias]
def DecAllOpaque (p : Nat → Prop) := ∀ n, Decidable (p n)
axiom lemOpaque (p : Nat → Prop) (d : DecAllOpaque p) : QQ (∀ n, p n) ↔ True
theorem semireducible_is_not_a_class (p : Nat → Prop) [∀ n, Decidable (p n)] :
    QQ (∀ n, p n) := by simp only [lemOpaque]
"#;

/// Lean's `isClass?` reads the class off the END of the binder type's `∀`
/// telescope and unfolds REDUCIBLE aliases on the way, so
/// `[∀ n, Decidable (p n)]` and `[DecAll p]` are instance slots, answered
/// from a local instance (`*_local`, and a `∀` local answering the alias
/// slot: `alias_from_pi`) or a global one (`*_global`). Refused, as in Lean:
/// no instance at all (`*_none`), and a SEMIREDUCIBLE definition that merely
/// unfolds to such a telescope — it is not a class, so nothing fills it.
#[test]
fn test_simp_instance_slot_is_a_telescope_ending_in_a_class() {
    assert_refused_exactly(
        PI_SLOTS,
        &[
            ("pi_none", "NoProgress"),
            ("alias_none", "NoProgress"),
            ("semireducible_is_not_a_class", "NoProgress"),
        ],
    );
}

const APPLIED_SLOTS: &str = r#"axiom QQ : Prop → Prop
axiom lemD (q : Prop) [Decidable q] : QQ q ↔ True
abbrev DecAll (p : Nat → Prop) := ∀ n, Decidable (p n)
theorem app_from_pi (p : Nat → Prop) [∀ n, Decidable (p n)] : QQ (p 3) := by simp only [lemD]
theorem app_from_alias (p : Nat → Prop) [DecAll p] : QQ (p 3) := by simp only [lemD]
theorem app_none (p : Nat → Prop) : QQ (p 3) := by simp only [lemD]
"#;

/// The other direction: a plain `[Decidable q]` slot at `q := p 3`, answered
/// by a LOCAL instance that is a family — written as a `∀` (`app_from_pi`) or
/// through a reducible alias (`app_from_alias`), which is a local instance
/// only because `isClass?` of its TYPE unfolds the alias.
#[test]
fn test_simp_instance_slot_is_answered_by_a_local_instance_family() {
    assert_refused_exactly(APPLIED_SLOTS, &[("app_none", "NoProgress")]);
}

const LOCAL_CONDITIONAL: &str = r#"theorem lcd_eq (f g : Nat → Nat) (p : Nat → Prop) (h : ∀ x, p x → f x = g x) (hp : p 3) :
    f 3 = g 3 := by simp only [h, hp]
theorem lcd_iff (q r p : Nat → Prop) (h : ∀ x, p x → (q x ↔ r x)) (hp : p 3) :
    q 3 = r 3 := by simp only [h, hp]
theorem lcd_prop (q p : Nat → Prop) (h : ∀ x, p x → q x) (hp : p 3) :
    q 3 := by simp only [h, hp]
theorem lcd_missing (q p : Nat → Prop) (h : ∀ x, p x → q x) :
    q 3 := by simp only [h]
theorem lcd_inst (q : Nat → Prop) (h : ∀ x, [Decidable (q x)] → q x) (d : ∀ x, Decidable (q x)) :
    q 3 := by simp only [h]
"#;

/// Lean's `synthesizeArgs` makes no difference between a global theorem and
/// a hypothesis: a CONDITIONAL local rule — an equation (`lcd_eq`), an `↔`
/// (`lcd_iff`), a plain proposition (`lcd_prop`) — fires when its premise is
/// discharged from the simp set, an instance premise is synthesized
/// (`lcd_inst`), and an undischarged premise is "no progress", never a loose
/// binder handed to the kernel (`lcd_missing`).
#[test]
fn test_simp_local_conditional_rule_discharges_its_premise() {
    assert_refused_exactly(LOCAL_CONDITIONAL, &[("lcd_missing", "NoProgress")]);
}

const SHADOWED: &str = r#"universe u
axiom RR {α : Sort u} : α → Prop
axiom ff {α : Sort u} : α → α
@[simp] axiom reg_lem {α : Sort u} (x : α) : RR x ↔ True
@[simp] axiom ff_lem {α : Sort u} (x : α) : ff x = x
theorem sh_registry_iff (n : Nat) (reg_lem : n = n) : RR n := by simp
theorem sh_registry_eq (n : Nat) (ff_lem : n = n) : ff n = n := by simp
theorem sh_registry_poly {β : Type u} (b : β) (reg_lem : b = b) : RR b := by simp
theorem sh_named_local (n m : Nat) (reg_lem : n = m) : RR n ↔ RR m := by simp only [reg_lem]
"#;

/// The `@[simp]` registry is not shadowed by the local context: a hypothesis
/// that happens to be NAMED like a registered lemma leaves the lemma in force
/// (`sh_registry_*`, the `↔` one at a concrete and at a polymorphic carrier).
/// A name WRITTEN in the simp list still resolves to the local first
/// (`sh_named_local` rewrites with the hypothesis `n = m`).
#[test]
fn test_simp_registry_lemma_survives_a_hypothesis_of_the_same_name() {
    assert_refused_exactly(SHADOWED, &[]);
}

const SIMPA_FALSE: &str = r#"axiom QQ : Nat → Prop
axiom nQ (n : Nat) : ¬ QQ n
theorem sa_using_false (h : QQ 1) : 1 = 2 := by simpa only [nQ] using h
theorem sa_using_already_false (h : False) : 1 = 2 := by simpa using h
theorem sa_using_term (h : ∀ n, QQ n) : 1 = 2 := by simpa only [nQ] using h 1
def sa_type_valued (h : QQ 1) : Nat := by simpa only [nQ] using h
theorem sa_mismatch (h : QQ 1 ∨ True) : 1 = 2 := by simpa only [nQ] using h
"#;

/// Lean's `simpa … using e` notes `e` as a hypothesis and simplifies it with
/// `simpGoal`; one that becomes `False` closes the goal and there is no
/// closing `exact` — for a hypothesis (`sa_using_false`), one that already
/// is `False`, a compound term (`sa_using_term`) and a goal that is not a
/// proposition (`sa_type_valued`). The near miss still fails: a term that
/// simplifies to anything else must match the goal (`sa_mismatch`).
#[test]
fn test_simpa_using_a_term_simplified_to_false_closes_the_goal() {
    let failed = failures(SIMPA_FALSE);
    assert_eq!(
        failed.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        ["sa_mismatch"],
        "only the mismatch is refused: {failed:?}"
    );
}

const LOCAL_CONJ: &str = r#"theorem lc_left (a b : Prop) (h : a ∧ b) : a := by simp only [h]
theorem lc_right (a b : Prop) (h : a ∧ b) : b := by simp only [h]
theorem lc_nested (a b c : Prop) (h : a ∧ b ∧ c) : c := by simp only [h]
theorem lc_forall (p q : Nat → Prop) (h : ∀ n, p n ∧ q n) : q 3 := by simp only [h]
theorem lc_neg (a b : Prop) (h : a ∧ ¬ b) : b = False := by simp only [h]
theorem lc_eq (f : Nat → Nat) (a : Prop) (h : a ∧ f 1 = 2) : f 1 = 2 := by simp only [h]
theorem lc_iff (a b c : Prop) (h : a ∧ (b ↔ c)) : b = c := by simp only [h]
theorem lc_near (a b c : Prop) (h : a ∧ b) : c := by simp only [h]
"#;

/// Lean's `preprocess` is one function for a global theorem and a local
/// hypothesis: `h : a ∧ b` yields the rules of `a` and of `b` (`h.1`, `h.2`),
/// recursively (`lc_nested`), under the hypothesis's own binders
/// (`lc_forall`), and each conjunct by its own shape — a negation
/// (`lc_neg`), an equation (`lc_eq`), an `↔` (`lc_iff`). A conjunction says
/// nothing about an unrelated proposition (`lc_near`).
#[test]
fn test_simp_local_conjunction_hypothesis_is_split_into_its_conjuncts() {
    assert_refused_exactly(LOCAL_CONJ, &[("lc_near", "NoProgress")]);
}

const CONJUNCT_FORALL: &str = r#"axiom P3 : Nat → Prop
axiom P4 : Nat → Prop
axiom conjAll : P3 0 ∧ ∀ n, P4 n
theorem gf_first : P3 0 := by simp only [conjAll]
theorem gf_inner : P4 5 := by simp only [conjAll]
"#;

/// OPEN, pinned as a refusal so it fails loudly the day it closes. Lean's
/// `preprocess.go` re-enters the `∀` telescope INSIDE a conjunct, so
/// `conjAll : P3 0 ∧ ∀ n, P4 n` yields the rule `P4 n = True` and pinned
/// v4.30.0-rc2 ACCEPTS `gf_inner`. Clean opens the statement's telescope once,
/// at the top, and makes `(∀ n, P4 n) = True` of that conjunct — sound, but
/// it does not match `P4 5`. Opening it needs a rule to carry its OWN binder
/// telescope: `bind_undetermined_binders`, `binding_violates_declared_domain`
/// and the level solver all read the binders off the DECLARATION's type, and
/// a conjunct's inner binders are not there.
///
/// TARGET: `gf_inner` elaborates (drop it from the refused list).
#[test]
fn test_simp_conjunct_under_its_own_forall_is_not_opened_yet() {
    assert_refused_exactly(CONJUNCT_FORALL, &[("gf_inner", "NoProgress")]);
}

const LOCAL_NE: &str = r#"theorem ne_goal (a : Nat) (h : a ≠ 0) : a ≠ 0 := by simp [h]
theorem ne_option (o : Option Nat) (h : o ≠ none) : o ≠ none := by simp [h]
theorem ne_not_goal (a : Nat) (h : a ≠ 0) : ¬ a = 0 := by simp [h]
theorem not_ne_goal (a : Nat) (h : ¬ a = 0) : a ≠ 0 := by simp [h]
theorem ne_forall (f : Nat → Nat) (h : ∀ x, f x ≠ 0) : f 3 ≠ 0 := by simp [h]
theorem ne_and_true (a : Nat) (h : a ≠ 0) : a ≠ 0 ∧ True := by simp [h]
theorem ne_bool (b : Bool) (h : b ≠ true) : b = false := by simp only [h]
theorem ne_term (a : Nat) (h : a + 1 ≠ 0 → a ≠ 0) (h2 : a + 1 ≠ 0) : a ≠ 0 := by simp [h h2]
theorem ne_at (a : Nat) (h : a ≠ 0) (h' : a = 0) : False := by simp [h] at h'
theorem ne_only_at (a : Nat) (h : a ≠ 0) (h' : a = 0) : False := by simp only [h] at h'
theorem ne_at_or (a b : Nat) (h : a ≠ 0) (h' : a = 0 ∨ b = 1) : b = 1 := by simp [h] at h'; exact h'
theorem ne_all (a : Nat) (h : a ≠ 0) : a ≠ 0 := by simp_all
theorem ne_all_or (a b : Nat) (h : a ≠ 0) (h' : a = 0 ∨ b = 1) : b = 1 := by simp_all
theorem ne_only_goal (a : Nat) (h : a ≠ 0) : a ≠ 0 := by simp only [h]
theorem ne_other (a : Nat) (h : a ≠ 0) : a ≠ 1 := by simp [h]
theorem ne_only_other (a : Nat) (h : a ≠ 0) : a ≠ 1 := by simp only [h]
theorem ne_only_ne_eq_other (a : Nat) (h : a ≠ 0) : a ≠ 2 := by simp only [h, ne_eq]
theorem ne_symm (a : Nat) (h : a ≠ 0) : 0 ≠ a := by simp [h]
theorem ne_eq_goal (a : Nat) (h : a ≠ 0) : a = 1 := by simp [h]
theorem ne_all_other (a : Nat) (h : a ≠ 0) : a ≠ 1 := by simp_all
"#;

/// A LOCAL disequality `h : a ≠ b` is Lean's `type.ne?` rule
/// `(a = b) = False` (`b = false` / `b = true` for a `Bool` literal), never
/// `(a ≠ b) = True`. Every line was run on pinned Lean 4.8.0 and
/// v4.30.0-rc2 (2026-11-13), which agree. With the default set's `ne_eq`
/// turning the goal `a ≠ 0` into `¬(a = 0)`, the `= True` reading could not
/// fire (`ne_goal`, `ne_option` were refused: "unsolved goals"), and it let
/// `simp only [h]` close the goal `a ≠ 0` (`ne_only_goal`), which both Leans
/// refuse ("simp made no progress"). The `at h'` and `simp_all` paths share
/// the rule. The disequality says nothing about another literal
/// (`ne_other`, `ne_only_other`, `ne_only_ne_eq_other`, `ne_all_other`), the
/// symmetric equation (`ne_symm`) or an equation goal (`ne_eq_goal`).
#[test]
fn test_simp_local_disequality_hypothesis_rewrites_its_equation_to_false() {
    assert_refused_exactly(
        LOCAL_NE,
        &[
            ("ne_only_goal", "NoProgress"),
            ("ne_other", "UnsolvedGoals"),
            ("ne_only_other", "NoProgress"),
            ("ne_only_ne_eq_other", "UnsolvedGoals"),
            ("ne_symm", "UnsolvedGoals"),
            ("ne_eq_goal", "NoProgress"),
            ("ne_all_other", "UnsolvedGoals"),
        ],
    );
}

const LOCAL_ARROW_FALSE: &str = r#"theorem af_goal_eq_false (P : Prop) (h : P → False) : P = False := by simp only [h]
theorem af_goal_iff (P : Prop) (h : P → False) : P ↔ False := by simp only [h]
theorem af_and (P Q : Prop) (h : P → False) : (P ∧ Q) = False := by simp [h]
theorem af_discharge (P : Prop) (hp : P) (h : P → False) : False := by simp only [h, hp]
theorem af_at (P : Prop) (h : P → False) (hp : P) : False := by simp only [h] at hp
theorem af_forall (q : Nat → Prop) (h : ∀ x, q x → False) : q 3 = False := by simp only [h]
theorem af_forall_discharge (q : Nat → Prop) (h : ∀ x, q x → False) (h3 : q 3) : False := by simp only [h, h3]
theorem af_not (P : Prop) (h : ¬ P) : P = False := by simp only [h]
theorem af_not_and (P Q : Prop) (h : ¬ P) : (P ∧ Q) = False := by simp [h]
theorem af_forall_not (q : Nat → Prop) (h : ∀ x, ¬ q x) : q 3 = False := by simp only [h]
theorem af_not_at (P : Prop) (h : ¬ P) (hp : P) : False := by simp only [h] at hp
theorem af_at_and (P Q : Prop) (h : P → False) (hq : P ∧ Q) : False := by simp [h] at hq
theorem af_and_right (P Q : Prop) (h : P → False) : (Q ∧ P) = False := by simp [h]
theorem af_ite (P : Prop) [Decidable P] (h : P → False) : (if P then 1 else 2) = 2 := by simp [h]
theorem af_curried (P Q : Prop) (h : Q → P → False) (hq : Q) : P = False := by simp only [h, hq]
theorem af_not_at_and (P Q : Prop) (h : ¬ P) (hq : P ∧ Q) : False := by simp [h] at hq
theorem af_not_and_right (P Q : Prop) (h : ¬ P) : (Q ∧ P) = False := by simp [h]
theorem af_not_ite (P : Prop) [Decidable P] (h : ¬ P) : (if P then 1 else 2) = 2 := by simp [h]
theorem af_not_curried (P Q : Prop) (h : Q → ¬ P) (hq : Q) : P = False := by simp only [h, hq]
"#;

/// A LOCAL `h : P → False` is NOT `¬P` to simp: Lean's `preprocess` reads a
/// negation off the `Not` head only, so the arrow takes its `isForall`
/// branch and becomes the conditional rule `P → (False = True)`. Every line
/// was run on pinned Lean 4.8.0, v4.30.0-rc2 and v4.36.0-rc2 (2026-11-13),
/// which agree on every verdict below. Reading the arrow as `P = False` let `simp only [h]` close
/// `P = False` (`af_goal_eq_false`), `P ↔ False` (`af_goal_iff`), the same
/// under a binder (`af_forall`) and a hypothesis `hp : P` (`af_at`), and
/// `simp [h]` close `(P ∧ Q) = False` (`af_and`), all of which every Lean
/// refuses. The conditional rule rewrites the goal `False` once its premise
/// is discharged (`af_discharge`), but not when a binder of the rule is
/// absent from its left-hand side (`af_forall_discharge`). Spelled with `¬`,
/// the hypothesis is still `P = False` (`af_not`, `af_not_and`,
/// `af_forall_not`, `af_not_at`).
///
/// Controls where only the `¬` spelling closes: the arrow rewrites neither a
/// hypothesis `hq : P ∧ Q` (`af_at_and`, no progress), nor the right conjunct
/// of `(Q ∧ P) = False` (`af_and_right`), nor an `if P` condition
/// (`af_ite`, both unsolved goals); and under a leading premise,
/// `h : Q → P → False` with `hq : Q` still makes no progress on `P = False`
/// (`af_curried`). Their `¬P` twins (`af_not_at_and`, `af_not_and_right`,
/// `af_not_ite`, `af_not_curried`) all close.
///
/// Lean refuses `af_and` and `af_and_right` with "unsolved goals" (its
/// default set leaves `P → ¬Q` / `Q → ¬P`, `h` unused); Clean's default set
/// has no rewrite of `(a ∧ b) = False`, so it refuses them with no progress.
/// Both refuse; the day Clean gains that rewrite these two flip to
/// `UnsolvedGoals` and this pin must move with them.
#[test]
fn test_simp_local_arrow_to_false_hypothesis_is_a_conditional_rule() {
    assert_refused_exactly(
        LOCAL_ARROW_FALSE,
        &[
            ("af_goal_eq_false", "NoProgress"),
            ("af_goal_iff", "NoProgress"),
            ("af_and", "NoProgress"),
            ("af_at", "NoProgress"),
            ("af_forall", "NoProgress"),
            ("af_forall_discharge", "NoProgress"),
            ("af_at_and", "NoProgress"),
            ("af_and_right", "NoProgress"),
            ("af_ite", "UnsolvedGoals"),
            ("af_curried", "NoProgress"),
        ],
    );
}

const CASE_TACTIC_NEGATIONS: &str = r#"theorem w_split (c : Prop) [Decidable c] : (if c then c else (c = False)) := by
  split
  · assumption
  · rename_i h; simp only [h]
theorem w_split_star (c : Prop) [Decidable c] : (if c then c else (c = False)) := by
  split
  · assumption
  · simp only [*]
theorem w_bycases (P : Prop) : P ∨ P = False := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr (by simp only [h])
theorem w_byc (P : Prop) (hp : P = False → False) : P := by
  by_contra h
  exact hp (by simp only [h])
theorem w_and_not (P Q : Prop) (h : ¬P ∧ ¬Q) : P = False := by simp only [h]
"#;

/// The negative-case hypothesis of `split`, `by_cases` and `by_contra` is
/// stated with the `Not` head, so `simp only [h]` rewrites its proposition
/// to `False`. Pinned Lean 4.8.0, v4.30.0-rc2 and v4.36.0-rc2 (2026-11-13)
/// close `w_split`, `w_split_star`, `w_bycases` and `w_and_not`, showing
/// `h : ¬c` / `h : ¬P`; Mathlib's `by_contra h` introduces `h : ¬P` (core
/// Lean has no `by_contra`). Each tactic used to state the case as
/// `c → False`, which simp reads as the conditional rule
/// `c → (False = True)`, not `c = False`.
#[test]
fn test_simp_case_tactic_negation_hypothesis_rewrites_to_false() {
    assert_refused_exactly(CASE_TACTIC_NEGATIONS, &[]);
}

const PUSH_NEG_AT: &str = r#"theorem w_pushneg (P Q : Prop) (h : ¬(P ∨ Q)) : P = False := by
  push_neg at h
  simp only [h]
theorem w_pushneg_exact (P Q : Prop) (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  push_neg at h
  exact h
theorem w_pushneg_unused (P Q : Prop) (h : ¬(P ∨ Q)) : True := by
  push_neg at h
  trivial
theorem w_pushneg_wrong_exact (P Q : Prop) (h : ¬(P ∨ Q)) : ¬P ∧ Q := by
  push_neg at h
  exact h
theorem w_pushneg_wrong_simp (P Q : Prop) (h : ¬(P ∨ Q)) : P = True := by
  push_neg at h
  simp only [h]
"#;

/// Mathlib's `push_neg` turns `h : ¬(P ∨ Q)` into `h : ¬P ∧ ¬Q`, after which
/// `simp only [h]` closes `P = False` (`w_pushneg`) and `exact h` closes
/// `¬P ∧ ¬Q` (`w_pushneg_exact`). Both were a known gap, refused with
/// `ProofNotProduced` once the pushed `h` was USED (`w_pushneg_unused`, which
/// never reads `h`, always closed); the pin said to move them to accepted the
/// day `push_neg at`'s hypothesis cast was fixed, and both now close and
/// kernel-check, as in Lean. The negative controls are what pinned Lean
/// refuses: `exact h` against a goal the pushed `h` does not state, and
/// `simp only [h]` driving `P = True` to `False = True`.
#[test]
fn test_push_neg_at_used_hypothesis_closes_as_in_lean() {
    assert_refused_exactly(
        PUSH_NEG_AT,
        &[
            ("w_pushneg_wrong_exact", "TypeMismatch"),
            ("w_pushneg_wrong_simp", "UnsolvedGoals"),
        ],
    );
}

const PRELUDE_NEGATIONS: &str = r#"theorem w_dite (c : Prop) [Decidable c] : c ∨ c = False :=
  if h : c then Or.inl h else Or.inr (by simp only [h])
theorem w_dite_exact_tac (c : Prop) [Decidable c] : c ∨ c = False := by
  exact if h : c then Or.inl h else Or.inr (by simp only [h])
def w_do (c : Prop) [Decidable c] : Id Nat := do
  if h : c then pure 0 else
    have _hc : c = False := by simp only [h]
    pure 1
theorem w_em (P : Prop) : P ∨ P = False := by
  cases Classical.em P with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (by simp only [h])
theorem w_rcases_em (P : Prop) : P ∨ P = False := by
  rcases Classical.em P with h | h
  · exact Or.inl h
  · exact Or.inr (by simp only [h])
theorem w_dec_cases (P : Prop) (d : Decidable P) : P ∨ P = False := by
  cases d with
  | isFalse h => exact Or.inr (by simp only [h])
  | isTrue h => exact Or.inl h
theorem w_arrow (c : Prop) (h : c → False) : c = False := by simp only [h]
"#;

/// The negative branch of a term-level `if h : c` (`w_dite`,
/// `w_dite_exact_tac`), a `do`-block `if h : c` (`w_do`), and of a case split
/// on `Classical.em` (`w_em`, `w_rcases_em`) or on a `Decidable` value
/// (`w_dec_cases`) is `h : ¬c`, with the `Not` head: pinned Lean 4.8.0,
/// v4.30.0-rc2 and v4.36.0-rc2 (2026-11-13) close all six and state
/// `Classical.em : ∀ p, p ∨ ¬p` and `Decidable.isFalse : ¬p → Decidable p`.
/// The builtin prelude stated both, and the `dite` else-binder, as the
/// unfolded `p → False`, which simp reads as a conditional rule. `w_arrow`,
/// the arrow spelled by hand, stays refused, as every Lean refuses it.
#[test]
fn test_simp_prelude_negation_hypothesis_rewrites_to_false() {
    assert_refused_exactly(PRELUDE_NEGATIONS, &[("w_arrow", "NoProgress")]);
}

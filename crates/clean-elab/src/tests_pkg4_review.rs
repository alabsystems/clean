// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PKG4 adversarial review arms: near-miss shapes around the three unifier
//! repairs (`ctxApprox` + `checkTypesAndAssign`, the unreduced-first App/App
//! comparison, the `Sort ?u` binder), each ground-truthed on the pinned
//! toolchain (`leanprover--lean4---v4.30.0-rc2`, builtin `Init` only).
//!
//! Three kinds of arm:
//!
//! * shapes pinned Lean ACCEPTS that the package's own arms do not reach —
//!   explicit mode (`@f _ _ …`), nested untyped binders, the same rows inside
//!   tactic blocks, a same-head comparison that must FALL BACK to the reduced
//!   one;
//! * shapes pinned Lean REJECTS, which must stay rejected: the repairs add
//!   solutions ahead of the historical path, and an arm that only ever asserts
//!   acceptance cannot see one that adds too many;
//! * one over-acceptance whose FACE the package changed (see
//!   [`test_review_unsolved_binder_type_is_still_auto_bound`]).

use crate::tests_pkg4_unifier::{assert_elaborates, elab_after};

const FN_BASE: &str = "\
universe u v w
def LInv {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
def RInv {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop := LInv f g
def Inj {α : Sort u} {β : Sort v} (f : α → β) : Prop := ∀ a b, f a = f b → a = b
def Surj {α : Sort u} {β : Sort v} (f : α → β) : Prop := ∀ b, ∃ a, f a = b
axiom myext {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β) (g : α → γ) (j : β → γ) : β → γ
theorem RInv.surj {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : RInv g f) : Surj f :=
  fun y => ⟨g y, h y⟩
theorem LInv.rinv {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : LInv g f) : RInv f g := h
theorem LInv.inj {α : Sort u} {β : Sort v} {g : β → α} {f : α → β} (h : LInv g f) : Inj f :=
  fun a b e => ((h a).symm.trans (congrArg g e)).trans (h b)
";

fn assert_refused(base: &str, target: &str, label: &str) {
    assert!(
        elab_after(base, target).is_some(),
        "{label}: pinned Lean REJECTS this declaration and Clean accepted it"
    );
}

// ---------------------------------------------------------------------------
// ctxApprox: explicit mode, nesting, and the rows' shape inside tactic blocks.
// ---------------------------------------------------------------------------

/// Explicit mode mints the inner metavariables from `_` HOLES rather than from
/// inserted implicits; every mix of given and elided type argument must
/// narrow the same way.
#[test]
fn test_review_ctx_approx_explicit_mode_holes_under_untyped_binder_elaborate() {
    assert_elaborates(
        FN_BASE,
        "theorem x1 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, @LInv _ _ g f) : True := True.intro\n\
         theorem x2 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, @LInv α _ g f) : True := True.intro\n\
         theorem x3 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, @LInv _ β g f) : True := True.intro\n",
        "`∃ g, @LInv _ _ g f` and its half-explicit forms",
    );
}

/// Two untyped binders, the inner metavariables minted two binders deep and
/// shared between conjuncts; and an untyped `∀` under an untyped `∃`.
#[test]
fn test_review_ctx_approx_nested_untyped_binders_elaborate() {
    assert_elaborates(
        FN_BASE,
        "theorem x4 {α : Sort u} {β : Sort v} (f : α → β)\n    \
         (h : ∃ g, ∃ g', LInv g f ∧ LInv g' f ∧ g = g') : True := True.intro\n\
         theorem x5 {α : Sort u} {β : Sort v} (f : α → β)\n    \
         (h : ∃ g, ∀ g', LInv g f → RInv g' f → g = g') : True := True.intro\n\
         theorem x6 {α : Sort u} {β : Sort v} (f : α → β) : (∀ g, LInv g f → True) :=\n  \
         fun _ _ => True.intro\n\
         theorem x7 {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β) (e : β → γ)\n    \
         (h : Inj (fun g => myext f g e)) : True := True.intro\n\
         theorem x8 {α : Sort u} {β : Sort v} (f : α → β) :\n    \
         (fun g => LInv g f) = (fun g => LInv g f) := rfl\n",
        "nested untyped binders against inner implicits",
    );
}

/// The statement is only half of a row: the bound `g` has to be USABLE at the
/// solved type afterwards — eliminated, matched, re-packed — and the same
/// statements have to elaborate as tactic-block goals.
#[test]
fn test_review_ctx_approx_solved_binder_is_usable_in_terms_and_tactics() {
    assert_elaborates(
        FN_BASE,
        "theorem y1 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, LInv g f) : ∃ g, LInv g f :=\n  \
         h.elim fun g hg => ⟨g, hg⟩\n\
         theorem y2 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, LInv g f) : ∃ g, LInv g f :=\n  \
         match h with | ⟨g, hg⟩ => ⟨_, hg⟩\n\
         theorem y3 {α : Sort u} {β : Sort v} (f : α → β) : (∃ g, LInv g f) → Inj f :=\n  \
         fun ⟨g, hg⟩ a b hab => ((hg a).symm.trans (congrArg g hab)).trans (hg b)\n\
         theorem y4 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, LInv g f) : ∃ g, LInv g f := by\n  \
         obtain ⟨g, hg⟩ := h\n  exact ⟨g, hg⟩\n\
         theorem y5 {α : Sort u} {β : Sort v} (f : α → β) (h : ∃ g, LInv g f) : ∃ g, LInv g f := by\n  \
         have h2 : ∃ g, LInv g f := h\n  exact h2\n\
         theorem y6 {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (hg : LInv g f) :\n    \
         ∃ g, LInv g f := by\n  refine ⟨?_, ?_⟩\n  · exact g\n  · exact hg\n\
         theorem y7 {α : Sort u} {β : Sort v} (f : α → β) (h : ∀ g, LInv g f → False) :\n    \
         ¬ ∃ g, LInv g f :=\n  fun ⟨g, hg⟩ => h _ hg\n",
        "the solved binder used in terms and tactic blocks",
    );
}

/// `dite` with its proposition elided and EXPLICIT `fun` branches, in implicit
/// and in explicit mode, as a term and under `exact`: `Or.inl`'s implicit is
/// minted inside the branch binder while `dite`'s `?α` lives outside it.
#[test]
fn test_review_ctx_approx_dite_branch_implicits_elaborate() {
    assert_elaborates(
        "",
        "theorem z1 {a b : Prop} [Decidable a] (h : a → b) : b ∨ ¬a :=\n  \
         dite _ (fun ha => Or.inl (h ha)) (fun hn => Or.inr hn)\n\
         theorem z2 {a b : Prop} [Decidable a] (h : a → b) : b ∨ ¬a :=\n  \
         @dite _ a _ (fun ha => Or.inl (h ha)) (fun hn => Or.inr hn)\n\
         theorem z3 {a b : Prop} [Decidable a] (h : a → b) : b ∨ ¬a := by\n  \
         exact dite _ (Or.inl ∘ h) Or.inr\n",
        "`dite _` with branch-minted implicits",
    );
}

// ---------------------------------------------------------------------------
// checkTypesAndAssign: more routes to the type-only implicit, and refusals.
// ---------------------------------------------------------------------------

/// The type-only implicit reached through dot-notation chains, explicit mode
/// with every argument a hole, a hypothesis stated as the UNFOLDED `∀`, and at
/// concrete types.
#[test]
fn test_review_check_types_type_only_implicit_routes_elaborate() {
    assert_elaborates(
        FN_BASE,
        "theorem t1 {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : LInv f g) : Surj f :=\n  \
         h.rinv.surj\n\
         theorem t2 {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : LInv f g) : Surj f :=\n  \
         @RInv.surj _ _ _ _ (@LInv.rinv _ _ _ _ h)\n\
         theorem t3 {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : ∀ x, f (g x) = x) :\n    \
         Surj f := RInv.surj h\n\
         theorem t4 {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : ∀ x, g (f x) = x) :\n    \
         Inj f := LInv.inj h\n\
         theorem t5 {f : Nat → Bool} {g : Bool → Nat} (h : ∀ x, f (g x) = x) : Surj f :=\n  \
         RInv.surj h\n",
        "type-only implicits through dot chains, `@`, unfolded hypotheses",
    );
}

/// REFUSALS. Unifying a metavariable's type with its value's type ADDS
/// solutions; it must not add wrong ones. Pinned Lean rejects both with
/// `Application type mismatch`: the inverse handed over in the WRONG
/// direction, generically and at concrete types where `α` and `β` differ.
#[test]
fn test_review_check_types_wrong_direction_inverse_is_refused() {
    assert_refused(
        FN_BASE,
        "theorem neg1 {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} (h : LInv g f) : Surj f :=\n  \
         RInv.surj h\n",
        "`RInv.surj` applied to a LEFT inverse",
    );
    assert_refused(
        FN_BASE,
        "theorem neg2 {f : Nat → Bool} {g : Bool → Nat} (h : ∀ x, g (f x) = x) : Surj f :=\n  \
         RInv.surj h\n",
        "`RInv.surj` applied to a left inverse at `Nat`/`Bool`",
    );
}

// ---------------------------------------------------------------------------
// Unreduced-first App/App comparison.
// ---------------------------------------------------------------------------

/// A metavariable under a DEFINED head whose body DISCARDS its argument:
/// `K ?x =?= K 5`. Reduced first, both sides are `0`, unification succeeds
/// with `?x` never assigned, and the declaration dies `contains free
/// variables`. Compared as written, `?x := 5` (Lean's `isDefEqApp`). Nested
/// and two-metavariable forms alongside.
#[test]
fn test_review_unreduced_head_argument_discarding_definition_assigns_meta() {
    assert_elaborates(
        "def K (n : Nat) : Nat := 0\n\
         def dbl (n : Nat) : Nat := n + n\n",
        "theorem k1 (f : Nat → Nat) (h : ∀ x, f (K x) = 0) : f (K 5) = 0 := h _\n\
         theorem k2 (f : Nat → Nat) (h : ∀ x, f (dbl (dbl x)) = x) : f (dbl (dbl 3)) = 3 := h _\n\
         theorem k3 (f : Nat → Nat) (h : ∀ x y, f (dbl x + dbl y) = x) :\n    \
         f (dbl 1 + dbl 2) = 1 := h _ _\n",
        "`K ?x =?= K 5` and nested same-head forms",
    );
}

/// The FALLBACK half, two more faces. `K 3` is only REDUCIBLY `0`, so the
/// as-written comparison has nothing to pair and the reduced one must still
/// run; and two spellings of one instance (`natMin` an `instance`, `natMin'` a
/// `def`) under the same projection-function head fail argument-first
/// (`natMin =?= natMin'` are different constants) and succeed once unfolded.
#[test]
fn test_review_unreduced_head_falls_back_to_reduced_comparison() {
    assert_elaborates(
        "def K (n : Nat) : Nat := 0\n\
         class MyMin (α : Type) where min : α → α → α\n\
         instance natMin : MyMin Nat := ⟨fun a b => a⟩\n\
         def natMin' : MyMin Nat := ⟨fun a b => a⟩\n",
        "theorem f1 (f : Nat → Nat) (h : ∀ x, f (K x) = 0) : f 0 = 0 := h 3\n\
         theorem f2 (a b : Nat) : @MyMin.min Nat natMin a b = @MyMin.min Nat natMin' a b := rfl\n\
         theorem f3 (a b : Nat) (f : Nat → Nat) (h : ∀ x, f (@MyMin.min Nat natMin x b) = x) :\n    \
         f (@MyMin.min Nat natMin' a b) = a := h a\n",
        "argument-first fails, the reduced comparison succeeds",
    );
}

// ---------------------------------------------------------------------------
// The `Sort ?u` binder.
// ---------------------------------------------------------------------------

/// The unannotated binder on EITHER side of `=`, over a dependent codomain,
/// under `funext`, and applied at `Prop`, a `Sort u` and a `Type u` carrier.
#[test]
fn test_review_untyped_binder_at_sort_level_shapes_elaborate() {
    assert_elaborates(
        "universe u v\n",
        "theorem s1 {α : Sort u} {β : α → Sort v} (f : ∀ a, β a) : (fun x => f x) = f := rfl\n\
         theorem s2 {α : Sort u} {β : α → Sort v} (f g : ∀ a, β a) (h : ∀ x, f x = g x) :\n    \
         (fun x => f x) = (fun x => g x) := funext h\n\
         theorem s3 {α : Sort u} : (fun x => x) = (fun (x : α) => x) := rfl\n\
         theorem s4 {α : Type u} (p : α → Prop) : (fun x => p x) = (fun x => p x) := rfl\n\
         def s5 (p : Prop) (h : p) : p := (fun x => x) h\n\
         def s6 {α : Sort u} (a : α) : α := (fun x => x) a\n\
         def s7 := fun x => x + 1\n\
         theorem s8 : s7 2 = 3 := rfl\n",
        "untyped binders across sorts",
    );
}

/// Unsolved binder types are refused; explicitly declared polymorphism remains usable.
#[test]
fn test_review_unsolved_binder_type_is_refused() {
    assert!(elab_after("", "def n1 := fun x => x\n").is_some());
    assert_elaborates(
        "def n1 {α : Sort u} (x : α) : α := x\n",
        "theorem n2 : n1 5 = 5 := rfl\ntheorem n3 (p : Prop) (h : p) : p := n1 h\n",
        "explicitly declared universe-polymorphic identity",
    );
}

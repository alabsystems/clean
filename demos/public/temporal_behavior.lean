-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Behavior-indexed temporal capability (two-language design §4.2, R5), the
-- FAITHFUL mirror of clean-tla's TLAsem M0 (crates/clean-tla/src/semantics.rs):
-- temporal formulas are predicates on BEHAVIORS (ω-sequences of states), □/◇/⇝
-- are the drop-shifted quantifiers
--
--   □F  ≡  λ b. ∀ n, F (drop b n)      ◇F  ≡  λ b. ∃ n, F (drop b n)
--   F ⇝ G  ≡  □(λ b. F b → ◇G b)
--
-- so a property proved here is definitionally the term the ty-certificate lane
-- rechecks. TLA+ appears nowhere — the temporal capability IS Clean notation;
-- the engine format (TLA+) stays internal to ty (the format firewall). Companion
-- to temporal_notation.lean, which uses the simpler Nat→Prop (LTL) model; this
-- file carries the genuine behavior-shift semantics with real funext + Nat-arith
-- proofs of the drop algebra. State = Nat for a concrete, self-contained demo.

def Behavior := Nat → Nat

-- The suffix of `b` starting at index `n`.
def drop (b : Behavior) (n : Nat) : Behavior := fun k => b (n + k)

def TBox     (F : Behavior → Prop) : Behavior → Prop := fun b => ∀ n, F (drop b n)
def TDiam    (F : Behavior → Prop) : Behavior → Prop := fun b => ∃ n, F (drop b n)
def TLeadsTo (F G : Behavior → Prop) : Behavior → Prop :=
  TBox (fun c => F c → TDiam G c)

prefix:100 "□" => TBox
prefix:100 "◇" => TDiam
infixl:50 " ~> " => TLeadsTo

-- ── the drop algebra (the semantic backbone; genuine funext + Nat-arith) ──

-- Dropping zero is the identity. NOT definitional (`0 + k` does not reduce to
-- `k` — Nat.add recurses on its second argument): a real funext + Nat.zero_add.
theorem drop_zero (b : Behavior) : drop b 0 = b :=
  by
    funext k
    exact congrArg b (Nat.zero_add k)

-- Dropping composes additively — the shift semigroup law (funext + add_assoc).
theorem drop_drop (b : Behavior) (n m : Nat) : drop (drop b n) m = drop b (n + m) :=
  funext (fun k => congrArg b (Eq.symm (Nat.add_assoc n m k)))

-- ── the temporal theorems, all in the □/◇/~> surface, all kernel-checked ──

-- □F entails F holds now (at the head, drop by 0).
theorem tbox_here (F : Behavior → Prop) (b : Behavior) (h : (□ F) b) : F b :=
  drop_zero b ▸ h 0

-- □ is monotone under (behaviorwise) formula implication.
theorem tbox_mono (F G : Behavior → Prop) (himp : ∀ c, F c → G c) (b : Behavior)
    (h : (□ F) b) : (□ G) b :=
  fun n => himp (drop b n) (h n)

-- □F entails ◇F — the suffix at 0 is a witness.
theorem tbox_implies_tdiam (F : Behavior → Prop) (b : Behavior) (h : (□ F) b) : (◇ F) b :=
  ⟨0, h 0⟩

-- F holds now ⇒ ◇F (an explicit-cast reflexivity witness).
theorem tdiam_here (F : Behavior → Prop) (b : Behavior) (h : F b) : (◇ F) b :=
  ⟨0, Eq.mpr (congrArg F (drop_zero b)) h⟩

-- □ is idempotent one way: □F ⊢ □□F. Needs the drop composition law to realign
-- the doubly-dropped suffix — a genuine temporal fact, not an unfolding.
theorem tbox_tbox (F : Behavior → Prop) (b : Behavior) (h : (□ F) b) : (□ (□ F)) b :=
  fun n k => drop_drop b n k ▸ h (n + k)

-- leads-to is reflexive: F ⇝ F (witness the current suffix, drop by 0).
theorem tleadsto_refl (F : Behavior → Prop) (b : Behavior) : (F ~> F) b :=
  fun n hf => ⟨0, Eq.mpr (congrArg F (drop_zero (drop b n))) hf⟩

-- ◇ unfolds to its raw existential (identity via defeq) — the elimination
-- bridge for def-headed ◇ terms.
theorem tdiam_unfold (F : Behavior → Prop) (b : Behavior) (h : (◇ F) b) :
    ∃ n, F (drop b n) := h

-- ◇ ABSORBS an outer drop: a witness m past suffix n is the witness n+m at
-- the head — the temporal shift-absorption law, via the drop semigroup.
theorem tdiam_of_shifted (G : Behavior → Prop) (b : Behavior) (n : Nat)
    (h : ∃ m, G (drop (drop b n) m)) : (◇ G) b :=
  @Exists.elim Nat (fun m => G (drop (drop b n) m)) ((◇ G) b) h
    (fun m hg => ⟨n + m, Eq.mpr (congrArg G (Eq.symm (drop_drop b n m))) hg⟩)

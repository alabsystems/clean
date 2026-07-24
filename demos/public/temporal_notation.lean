-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Temporal capability (two-language design §4.2, R5): □ ◇ ~> as ordinary
-- fixed-arity Clean notation over a transition-semantics vocabulary, with
-- GENUINE kernel-checked temporal theorems (not just trivial holds). TLA+
-- appears nowhere — the temporal capability IS Clean notation; the engine
-- format (TLA+) stays internal to ty (the format firewall). The shapes mirror
-- clean-tla's TLAsem M0 (the □/◇/~> semantics of semantics.rs), so a property
-- stated here is definitionally the term the ty-certificate lane proves.

def Always     (p : Nat → Prop) : Prop := ∀ n, p n
def Eventually (p : Nat → Prop) : Prop := ∃ n, p n
def LeadsTo (p q : Nat → Prop) : Prop := ∀ n, p n → ∃ m, q m

prefix:100 "□" => Always
prefix:100 "◇" => Eventually
infixl:50 " ~> " => LeadsTo

-- The pretty forms ARE the real terms — definitional equality, kernel-checked.
theorem box_unfolds     (p : Nat → Prop) : (□ p) = Always p := rfl
theorem diamond_unfolds (p : Nat → Prop) : (◇ p) = Eventually p := rfl
theorem leadsto_unfolds (p q : Nat → Prop) : (p ~> q) = LeadsTo p q := rfl

-- □p entails p holds at every point — in particular at 0.
theorem box_holds_at_zero (p : Nat → Prop) (h : □ p) : p 0 := h 0

-- □ is monotone under pointwise implication (real universal reasoning).
theorem box_mono (p q : Nat → Prop) (himp : ∀ n, p n → q n) (h : □ p) : □ q :=
  fun n => himp n (h n)

-- always ⇒ eventually: a genuine □ → ◇ fact needing a witness.
theorem box_implies_diamond (p : Nat → Prop) (h : □ p) : Eventually p := ⟨0, h 0⟩

-- leads-to is reflexive.
theorem leadsto_refl (p : Nat → Prop) : p ~> p := fun n hp => ⟨n, hp⟩

-- always-eventually (the □◇ shape of fairness / infinitely-often).
def infinitely_often (p : Nat → Prop) : Prop := □ fun n => ◇ fun m => p (n + m)

-- □ distributes over pointwise conjunction: if p and q each hold everywhere,
-- so does their conjunction.
theorem box_and (p q : Nat → Prop) (hp : □ p) (hq : □ q) : □ fun n => And (p n) (q n) :=
  fun n => And.intro (hp n) (hq n)

-- ◇ unfolds to the underlying existential (definitional, kernel-checked): the
-- pretty notation IS the real term. Also the bridge the eliminators below use.
theorem diamond_unfold (p : Nat → Prop) (h : ◇ p) : ∃ n, p n := h

-- ◇ is monotone under pointwise implication — transport the witness.
theorem diamond_mono (p q : Nat → Prop) (himp : ∀ n, p n → q n) (h : ◇ p) : ◇ q :=
  @Exists.elim Nat p (◇ q) (diamond_unfold p h) (fun n hpn => ⟨n, himp n hpn⟩)

-- leads-to is TRANSITIVE: compose the two reachability witnesses. This is the
-- core temporal chaining principle (P ⇝ Q, Q ⇝ R ⊢ P ⇝ R) — a genuine proof,
-- not a definitional unfolding.
theorem leadsto_trans (p q r : Nat → Prop) (h1 : p ~> q) (h2 : q ~> r) : p ~> r :=
  fun n hp => Exists.elim (h1 n hp) (fun m hqm => h2 m hqm)

-- □q makes anything lead to q (the always-antecedent of leads-to).
theorem box_leadsto (p q : Nat → Prop) (h : □ q) : p ~> q :=
  fun n _hp => ⟨n, h n⟩

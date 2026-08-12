-- The Exists elaboration surface that WORKS (Iris-lane probes,
-- pinned 2026-08-09): anonymous constructor, Exists.elim, and
-- match-on-Exists all elaborate; only explicit `Exists.intro` has an
-- implicit-predicate inference gap (pinned separately as p23).
def P (n : Nat) : Prop := Nat.zero = Nat.zero

theorem e3 : ∃ n : Nat, P n := ⟨Nat.zero, rfl⟩
def e4 (h : ∃ n : Nat, P n) : Nat := Nat.zero
theorem e5 (h : ∃ n : Nat, P n) : True :=
  Exists.elim h (fun _ _ => True.intro)
theorem e6 (h : ∃ n : Nat, P n) : True :=
  match h with
  | ⟨_, _⟩ => True.intro

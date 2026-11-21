inductive Run : Nat → Nat → Prop where
  | stop (n : Nat) : Run 0 n
  | step (budget a b : Nat) : a + 1 = b → Run budget b → Run (budget + 1) a

inductive Reaches : Nat → Nat → Prop where
  | refl (k : Nat) : Reaches k k
  | step (a b c : Nat) : a + 1 = b → Reaches b c → Reaches a c

theorem reaches_exec (a b : Nat) (h : Reaches a b) (fuel : Nat) (execution : Run fuel b) :
    ∃ budget, Run budget a := by
  induction h with
  | refl k => exact ⟨fuel, execution⟩
  | step a b c hs _ ih =>
    obtain ⟨budget, proof⟩ := ih execution
    exact ⟨budget + 1, Run.step budget a b hs proof⟩

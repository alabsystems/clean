-- FIXED 2026-08-10: not an inference gap — the prelude declared
-- Exists.intro's predicate binder EXPLICIT ((p : α → Prop); Lean:
-- implicit), so the witness argument matched the predicate slot.
-- Same prelude-fidelity class as the Option type-former bug (P18).
def P (n : Nat) : Prop := Nat.zero = Nat.zero
theorem e2 : ∃ n : Nat, P n := Exists.intro Nat.zero rfl

theorem e1 : Exists P := Exists.intro Nat.zero rfl

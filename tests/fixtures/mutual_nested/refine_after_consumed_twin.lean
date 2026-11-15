-- Twin of `refine_after_consumed.lean`: after `cases h` the first component
-- is `s.next`, never `s.next + 1`; Lean refuses the claim.
structure MS where
  locals : List Nat
  next : Nat

def run (s : MS) : Except String ((Nat × Nat) × MS) :=
  .ok ((s.next, s.next + 1), { s with next := s.next + 2 })

theorem run_eq (s : MS) :
    run s = .ok ((s.next, s.next + 1), { s with next := s.next + 2 }) := rfl

theorem run_ok_twin {s s' : MS} {ids : Nat × Nat} (h : run s = .ok (ids, s')) :
    ids.1 = s.next + 1 ∧ s'.next = s.next + 2 := by
  rw [run_eq] at h
  cases h
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

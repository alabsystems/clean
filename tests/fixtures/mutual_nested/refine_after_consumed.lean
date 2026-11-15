-- `refine`'s holes see the goal's context only: a hypothesis a tactic
-- consumed (`cases h` on a constructor equation clears `h` and substitutes
-- `ids`/`s'`; `subst h`) and a `mutual` block's sibling (an auxiliary
-- declaration, hidden from the goal) are not revived in the new goals.
-- Shape of trust-ir's `Sem.bindFreshPair_ok` (`Semantics/Monad.lean`).
structure MS where
  locals : List Nat
  next : Nat

def run (s : MS) : Except String ((Nat × Nat) × MS) :=
  .ok ((s.next, s.next + 1), { s with next := s.next + 2 })

theorem run_eq (s : MS) :
    run s = .ok ((s.next, s.next + 1), { s with next := s.next + 2 }) := rfl

theorem run_ok {s s' : MS} {ids : Nat × Nat} (h : run s = .ok (ids, s')) :
    ids.1 + 1 = ids.2 ∧ s'.next = s.next + 2 := by
  rw [run_eq] at h
  cases h
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

theorem subst_refine {x y : Nat} {ids : Nat × Nat} (h : (x, y) = ids) :
    ids.1 = x ∧ ids.2 = y := by
  subst h
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

mutual
theorem refine_a (n : Nat) : n = n ∧ True := by
  refine ⟨?_, ?_⟩
  · rfl
  · exact True.intro
theorem refine_b (n : Nat) : True ∧ n = n := by
  refine ⟨?_, ?_⟩
  · exact True.intro
  · rfl
end

-- Gap G66: a name given inside a focused block — `rename_i` under `·`,
-- `case succ m =>` — must reach the terms the block elaborates.
theorem rename_bullet (p : Nat) : p = 0 ∨ ∃ m, p = m + 1 := by
  cases p
  · exact Or.inl rfl
  · rename_i m
    exact Or.inr ⟨m, rfl⟩

theorem case_names (p : Nat) : p = 0 ∨ ∃ m, p = m + 1 := by
  cases p
  case zero => exact Or.inl rfl
  case succ m => exact Or.inr ⟨m, rfl⟩

inductive P where
  | leaf : Nat → P
  | conj : List P → P

theorem rename_nested (p : P) : ∃ n, p = .leaf n ∨ ∃ l, p = .conj l := by
  cases p
  · rename_i n
    exact ⟨n, Or.inl rfl⟩
  · rename_i l
    exact ⟨0, Or.inr ⟨l, rfl⟩⟩

-- `rename_i x y` names the last two inaccessible locals in context order:
-- `x` is the `Nat` field, `y` the `Bool` one.
theorem rename_order (p : Nat × Bool) : p.1 = p.1 := by
  cases p
  rename_i x y
  show x = x
  rfl

-- Fields of an earlier `cases` stay inaccessible after a later one.
theorem rename_two_levels (p q : Option Nat) : True := by
  cases p <;> cases q
  · trivial
  · trivial
  · trivial
  · rename_i x y
    have hx : x = x := rfl
    trivial

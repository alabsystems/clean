-- Brick B6: a `mutual` block's members are auxiliary declarations while
-- their bodies elaborate. A body that NAMES a sibling still reaches it.
mutual
theorem r1 : True := by exact r2
theorem r2 : True := True.intro
end

mutual
theorem s1 (n : Nat) : n + 0 = n := by
  have h := s2 n
  exact h
theorem s2 (n : Nat) : n + 0 = n := rfl
end

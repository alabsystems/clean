-- Class (88), the face still OPEN: with two matched columns, the matrix
-- compiler binds the first column's pattern variable (`n`) as an alias of
-- its own field, while the generalized hypothesis is stated over that field,
-- so `h : i + 1 < n + 1` does not mention the user's `n`. Pinned Lean 4.8.0
-- accepts; Clean refuses (fail-closed).
theorem pin_alias_twin : ∀ (n i : Nat), i < n → i < n
  | 0, _, h => h
  | _ + 1, 0, h => h
  | n + 1, i + 1, h => (h : n + 1 < i + 1)

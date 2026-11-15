-- Refused by Lean 4.8 and Clean: `P.listBeq_refl xs.reverse` is not on a subterm.
inductive P where
  | leaf : P
  | conj : List P → P
mutual
def P.beq : P → P → Bool
  | .leaf, .leaf => true
  | .conj x, .conj y => P.listBeq x y
  | _, _ => false
def P.listBeq : List P → List P → Bool
  | [], [] => true
  | p :: ps, q :: qs => P.beq p q && P.listBeq ps qs
  | _, _ => false
end
mutual
theorem P.beq_refl : ∀ a : P, P.beq a a = true
  | .leaf => rfl
  | .conj xs => P.listBeq_refl xs.reverse
theorem P.listBeq_refl : ∀ as : List P, P.listBeq as as = true
  | [] => rfl
  | p :: ps => by
      show (P.beq p p && P.listBeq ps ps) = true
      rw [P.beq_refl p, P.listBeq_refl ps]
      rfl
end

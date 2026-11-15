-- Block 13 twin: the sibling call on the major premise itself is not
-- structural (Lean: "fail to show termination").
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
theorem P.beq_eq : ∀ {a b : P}, P.beq a b = true → a = b := by
  intro a b h
  exact P.beq_eq h
theorem P.listBeq_eq : ∀ {as bs : List P}, P.listBeq as bs = true → as = bs := by
  intro as bs h
  exact P.listBeq_eq h
end

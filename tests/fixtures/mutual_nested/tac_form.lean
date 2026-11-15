-- Block 13 (trust-ir `Proofs/PredLatticeProps.lean`, `Pred.beq_eq` /
-- `Pred.listBeq_eq`): the tactic-form theorem block, end to end — nested
-- `cases a <;> cases b` (B5), `h` following `cases` (class (80)), sibling
-- calls inside the proofs (the lift), and the siblings hidden from `simp_all`
-- (B6).
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
  cases a <;> cases b <;> simp only [P.beq, Bool.and_eq_true] at h <;> first
    | rfl
    | (rename_i x y; exact congrArg P.conj (P.listBeq_eq h))
    | exact absurd h (by simp)
theorem P.listBeq_eq : ∀ {as bs : List P}, P.listBeq as bs = true → as = bs := by
  intro as bs h
  cases as with
  | nil => cases bs with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [P.listBeq])
  | cons p ps =>
    cases bs with
    | nil => exact absurd h (by simp [P.listBeq])
    | cons q qs =>
      simp only [P.listBeq, Bool.and_eq_true] at h
      have hpq := P.beq_eq h.1
      have hps := P.listBeq_eq h.2
      subst q
      subst qs
      rfl
end

-- Gap G23 brick B3 (judge k1): `simp [f]`, `simp only [f, Bool.and_eq_true] at h`
-- and `rw [f.eq_N]` on lifted members; s3 meets a catch-all on mixed constructors.
inductive P where
  | leaf : Nat → P
  | conj : List P → P
mutual
def P.beq : P → P → Bool
  | .leaf a, .leaf b => a == b
  | .conj x, .conj y => P.listBeq x y
  | _, _ => false
def P.listBeq : List P → List P → Bool
  | [], [] => true
  | p :: ps, q :: qs => P.beq p q && P.listBeq ps qs
  | _, _ => false
end
theorem s1 (x y : List P) : P.beq (.conj x) (.conj y) = P.listBeq x y := by simp [P.beq]
theorem s2 (p q : P) (ps qs : List P) (h : P.listBeq (p :: ps) (q :: qs) = true) : P.beq p q = true := by
  simp only [P.listBeq, Bool.and_eq_true] at h
  exact h.1
theorem s3 (n : Nat) (y : List P) : P.beq (.leaf n) (.conj y) = false := by simp [P.beq]
theorem r2 (x y : List P) : P.beq (.conj x) (.conj y) = P.listBeq x y := by rw [P.beq.eq_2]
theorem n1 : ∀ (a b : Nat), P.beq (P.leaf a) (P.leaf b) = (a == b) := P.beq.eq_1
theorem n2 : ∀ (x_2 y : List P), P.beq (P.conj x_2) (P.conj y) = P.listBeq x_2 y := P.beq.eq_2
theorem n3 : P.listBeq [] [] = true := P.listBeq.eq_1
theorem n4 : ∀ (p : P) (ps : List P) (q : P) (qs : List P),
    P.listBeq (p :: ps) (q :: qs) = (P.beq p q && P.listBeq ps qs) := P.listBeq.eq_2

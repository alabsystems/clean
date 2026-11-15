-- Class (81): `cases h` on an equation solves it as Lean's `unifyEqs?`:
-- distinct constructors close the goal, equal ones leave their fields'
-- equations (heterogeneous `noConfusion` for a parameterized type).
theorem ctor_mismatch (x : Nat) (rest : List Nat) (h : x :: rest = []) : False := by
  cases h

theorem ctor_inj (ys : List Nat)
    (h : (Except.ok [] : Except String (List Nat)) = Except.ok ys) : ys = [] := by
  cases h
  rfl

theorem ctor_inj_two (a b : Nat) (as bs : List Nat) (h : a :: as = b :: bs) : a = b ∧ as = bs := by
  cases h
  exact ⟨rfl, rfl⟩

inductive P where
  | leaf : Nat → P
  | conj : List P → P

theorem nested_mismatch (n : Nat) (l : List P) (h : P.leaf n = P.conj l) : False := by
  cases h

theorem nested_inj (n m : Nat) (h : P.leaf n = P.leaf m) : n = m := by
  cases h
  rfl

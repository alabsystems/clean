-- Class (80): `cases x` reverts every hypothesis that mentions `x` and
-- re-introduces it, under its own name, after each case's fields.
theorem bool_dep (b : Bool) (h : b = true) : b = true := by
  cases b with
  | false => exact h
  | true => rfl

inductive P where
  | leaf : Nat → P
  | conj : List P → P

def P.isLeaf : P → Bool
  | .leaf _ => true
  | .conj _ => false

theorem nested_dep (p : P) (h : p.isLeaf = true) : ∃ n, p = .leaf n := by
  cases p with
  | leaf n => exact ⟨n, rfl⟩
  | conj xs => exact absurd h (fun h' => Bool.noConfusion h')

theorem order_kept (q : Nat) (p : P) (h : p.isLeaf = true) (k : q = q) : ∃ n, p = .leaf n := by
  cases p
  · rename_i n
    exact ⟨n, rfl⟩
  · exact absurd h (fun h' => Bool.noConfusion h')

theorem chain_dep (b : Bool) (h : b = true) (h2 : h = h) : b = true := by
  cases b with
  | false => exact h
  | true => exact h

theorem intro_dep : ∀ (b : Bool), b = true → b = true := by
  intro b h
  cases b with
  | false => exact h
  | true => rfl

theorem intro_nested_dep : ∀ (q : Nat) (p : P), p.isLeaf = true → q = q → ∃ n, p = .leaf n := by
  intro q p h k
  cases p with
  | leaf n => exact ⟨n, rfl⟩
  | conj xs => exact absurd h (fun h' => Bool.noConfusion h')

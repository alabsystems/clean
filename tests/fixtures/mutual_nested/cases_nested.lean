-- Brick B5 (class (92)): `cases` on a nested inductive. Clean's kernel
-- `P.casesOn` also takes the `List P` motive and the `nil`/`cons` minors.
inductive P where
  | leaf : Nat → P
  | conj : List P → P

def P.isLeaf : P → Bool
  | .leaf _ => true
  | .conj _ => false

theorem with_alts (p : P) : p.isLeaf = true ∨ p.isLeaf = false := by
  cases p with
  | leaf n => exact Or.inl rfl
  | conj xs => exact Or.inr rfl

theorem bullets (p : P) : p.isLeaf = true ∨ p.isLeaf = false := by
  cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem case_tags (p : P) : p.isLeaf = true ∨ p.isLeaf = false := by
  cases p
  case conj xs => exact Or.inr rfl
  case leaf n => exact Or.inl rfl

theorem rcases_alts (p : P) : p.isLeaf = true ∨ p.isLeaf = false := by
  rcases p with n | xs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem obtain_alts (p : P) : p.isLeaf = true ∨ p.isLeaf = false := by
  obtain n | xs := p
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fields_named (p : P) : (∃ n, p = .leaf n) ∨ ∃ xs, p = .conj xs := by
  cases p with
  | leaf n => exact Or.inl ⟨n, rfl⟩
  | conj xs => exact Or.inr ⟨xs, rfl⟩

theorem two_levels (p q : P) : p.isLeaf = true ∨ q.isLeaf = false ∨ q.isLeaf = true := by
  cases p <;> cases q <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

inductive C where
  | int : Int → C
  | agg : List C → C
  | record : List (String × C) → C

theorem pair_intermediate (c : C) : (∃ i, c = .int i) ∨ (∃ l, c = .agg l) ∨ ∃ l, c = .record l := by
  cases c with
  | int i => exact Or.inl ⟨i, rfl⟩
  | agg l => exact Or.inr (Or.inl ⟨l, rfl⟩)
  | record l => exact Or.inr (Or.inr ⟨l, rfl⟩)

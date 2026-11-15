-- B5 (class (92)): `cases` on a member of a MUTUAL block. Clean's kernel
-- `A.casesOn` takes both members' motives and minors.
mutual
inductive A where
  | base : A
  | ofB : B → A
inductive B where
  | ofA : A → B
end

theorem mutual_first (a : A) : a = .base ∨ ∃ b, a = .ofB b := by
  cases a with
  | base => exact Or.inl rfl
  | ofB b => exact Or.inr ⟨b, rfl⟩

theorem mutual_second (b : B) : ∃ a, b = .ofA a := by
  cases b with
  | ofA a => exact ⟨a, rfl⟩

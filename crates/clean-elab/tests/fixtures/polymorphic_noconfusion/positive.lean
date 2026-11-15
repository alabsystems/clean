theorem optionParam {α : Type u} (a : α) (h : (none : Option α) = some a) : False := by
  simp only [reduceCtorEq] at h

theorem optionReverse {α : Type u} (a : α) (h : some a = (none : Option α)) : False := by
  simp only [reduceCtorEq] at h

theorem listParam {α : Type u} (a : α) (xs : List α) (h : ([] : List α) = a :: xs) : False := by
  simp only [reduceCtorEq] at h

theorem sumParam {α : Type u} {β : Type v} (a : α) (b : β)
    (h : (Sum.inl a : Sum α β) = Sum.inr b) : False := by
  simp only [reduceCtorEq] at h

inductive PolyPayload (α : Type u) : Type u where
  | wrap : α → PolyPayload α

theorem customParam {α : Type u} (a : PolyPayload α)
    (h : (none : Option (PolyPayload α)) = some a) : False := by
  simp only [reduceCtorEq] at h

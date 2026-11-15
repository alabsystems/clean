-- `simp … at h` on each case of a `cases` (`<;>`, `all_goals`): the
-- simplified hypothesis is numbered at its goal's own binder depth.
inductive Q where
  | leaf : Q
  | node : Nat → Q

def Q.isLeaf : Q → Bool
  | .leaf => true
  | .node _ => false

theorem y1 : ∀ (a : Q), a.isLeaf = true → True := by
  intro a h
  cases a <;> simp only [Q.isLeaf] at h <;> trivial

theorem y2 (a : Q) (h : a.isLeaf = true) : True := by
  cases a <;> simp only [Q.isLeaf] at h <;> trivial

theorem y4 : ∀ (a : Q), a.isLeaf = true → True := by
  intro a h
  cases a
  all_goals simp only [Q.isLeaf] at h
  all_goals trivial

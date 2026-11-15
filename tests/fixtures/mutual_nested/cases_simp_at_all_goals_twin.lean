-- Twin: after `simp … at h` the `leaf` case still has its goal
-- `Q.leaf = Q.leaf`; nothing closes it.
inductive Q where
  | leaf : Q
  | node : Nat → Q

def Q.isLeaf : Q → Bool
  | .leaf => true
  | .node _ => false

theorem z_twin : ∀ (a : Q), a.isLeaf = true → a = .leaf := by
  intro a h
  cases a <;> simp only [Q.isLeaf] at h

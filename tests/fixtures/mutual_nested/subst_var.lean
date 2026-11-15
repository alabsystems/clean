-- Lean's `subst x` with `x` a variable: the oldest equation `x = e` or
-- `e = x` eliminates `x` (block 13: `subst q` after `have hpq : p = q`).
theorem sv_rhs (p q : Nat) (h : p = q) (k : q + 0 = q) : q = p := by
  subst q
  rfl

theorem sv_lhs (p q : Nat) (h : p = q) : q = p := by
  subst p
  rfl

theorem sv_list (p q : Nat) (ps qs : List Nat) (h1 : p = q) (h2 : ps = qs) : p :: ps = q :: qs := by
  subst q
  subst qs
  rfl

-- Consumer module for the multi-component partial `end`: both names spelled
-- the way Lean 4.30.0-rc2 spells them.
theorem uses_suffix_mid : A.mid = 2 := rfl

theorem uses_suffix_deep : A.B.C.deep = 1 := rfl

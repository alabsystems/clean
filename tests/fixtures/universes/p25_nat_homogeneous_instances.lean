-- Lean core's homogeneous Nat instances (instAddNat/instMulNat/instSubNat)
-- existed in-tree but were #[cfg(test)]-gated and never registered, so a
-- direct `Add.add a b` failed instance synthesis while `a + b` (the
-- heterogeneous instHAddNat chain) worked. Found by the 2026-08-10
-- prelude-fidelity audit; wired into init_prelude_core + the instance table.
def a1 : Nat := Add.add 1 2
def m1 : Nat := Mul.mul 3 4
def s1 : Nat := Sub.sub 9 4
theorem a1v : Add.add 1 2 = 3 := rfl
theorem m1v : Mul.mul 3 4 = 12 := rfl
theorem s1v : Sub.sub 9 4 = 5 := rfl
theorem plus_still : 1 + 2 = 3 := rfl

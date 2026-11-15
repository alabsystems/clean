-- Gap G23 brick B3 (pos_grandchild): `simp [f]` through the pair intermediate;
-- the cons equation splits the pair as Lean's `(_, c) :: fs` equation does.
inductive C where
  | int : Nat → C
  | record : List (Nat × C) → C
mutual
def C.sz : C → Nat
  | .int n => n
  | .record fs => C.fsz fs
def C.fsz : List (Nat × C) → Nat
  | [] => 0
  | (_, c) :: fs => C.sz c + C.fsz fs
end
theorem good : C.sz (.record [(0, .int 2), (1, .int 3)]) = 5 := by simp [C.sz, C.fsz]
theorem eqn (fs : List (Nat × C)) : C.sz (.record fs) = C.fsz fs := by simp [C.sz]
theorem eqn2 (s : Nat) (c : C) (fs : List (Nat × C)) : C.fsz ((s, c) :: fs) = C.sz c + C.fsz fs := by simp [C.fsz]
theorem n2 : ∀ (fst : Nat) (c : C) (fs : List (Nat × C)), C.fsz ((fst, c) :: fs) = C.sz c + C.fsz fs := C.fsz.eq_2

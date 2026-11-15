-- False twin of pair_decide.lean (judge k2 g1f).
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
theorem g1f : C.sz (.record [(0, .int 2)]) = 3 := by decide

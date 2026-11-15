-- Brick B2 (judge k2 g1, g2): `decide` through the pair intermediate.
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
theorem g1 : C.sz (.record [(0, .int 2)]) = 2 := by decide
theorem g2 : C.sz (.record [(0, .int 2), (1, .int 3)]) = 5 := by decide

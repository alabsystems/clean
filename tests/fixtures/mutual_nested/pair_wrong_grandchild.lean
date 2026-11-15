-- Brick B2 (design-direct-rec neg_grandchild_wrong, stated by `decide`): a
-- grandchild through the pair must be counted once, not dropped or doubled.
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
theorem bad : C.sz (.record [(0, .int 2), (1, .int 3)]) = 6 := by decide

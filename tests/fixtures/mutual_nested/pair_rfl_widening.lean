-- Widening (judge k2 g3r, docs/DECISIONS.md R45): the defining equation
-- through the pair holds by `rfl` on open terms; Lean 4.8's well-founded
-- members do not reduce there.
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
theorem g3r (s : Nat) (c : C) (fs : List (Nat × C)) :
    C.fsz ((s, c) :: fs) = C.sz c + C.fsz fs := rfl

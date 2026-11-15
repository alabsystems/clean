-- False twin of pair_rfl_widening.lean.
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
theorem g3r_twin (s : Nat) (c : C) (fs : List (Nat × C)) :
    C.fsz ((s, c) :: fs) = C.sz c := rfl

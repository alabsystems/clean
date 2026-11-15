-- False twin of pair_intermediate_size.lean.
inductive C where
  | int : Nat → C
  | record : List (Nat × C) → C

mutual
def C.size : C → Nat
  | .int _ => 1
  | .record fs => if C.fieldsSmall fs then 1 else 2
def C.fieldsSmall : List (Nat × C) → Bool
  | [] => true
  | (_, c) :: fs => C.size c == 0 && C.fieldsSmall fs
end

theorem s1_twin : C.size (.record [(0, .int 1)]) = 1 := by decide

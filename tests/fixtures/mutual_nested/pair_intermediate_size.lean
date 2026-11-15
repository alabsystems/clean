-- Brick B2, transparent intermediate: the recursive call goes through the pair
-- `Nat × C` (`String × Constant` in trust-ir `Constant.fieldsHaveSymbolAddr`,
-- Constant.lean:146; `Value.ofConstantFieldList`, Aggregate.lean:594).
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

theorem s1 : C.size (.record [(0, .int 1)]) = 2 := by decide

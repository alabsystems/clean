-- Block 7 (trust-ir Semantics/Aggregate.lean:594): the pair intermediate
-- `String × C`, whose first component the result keeps.
inductive C where
  | int : Int → C
  | bool : Bool → C
  | aggregate : List C → C
  | record : List (String × C) → C
  | splat : C → Nat → C
inductive V where
  | int : Nat → Int → V
  | bool : Bool → V
  | aggregate : List V → V
  | record : List (String × V) → V

mutual
def V.ofConstant : C → V
  | .int n => .int 64 n
  | .bool b => .bool b
  | .aggregate cs => .aggregate (V.ofConstantList cs)
  | .record fs => .record (V.ofConstantFieldList fs)
  | .splat c n => .aggregate (List.replicate n (V.ofConstant c))
def V.ofConstantList : List C → List V
  | [] => []
  | c :: cs => V.ofConstant c :: V.ofConstantList cs
def V.ofConstantFieldList : List (String × C) → List (String × V)
  | [] => []
  | (n, c) :: rest => (n, V.ofConstant c) :: V.ofConstantFieldList rest
end
theorem o1 : V.ofConstant (.record [("a", .int 1)]) = .record [("a", .int 64 1)] := rfl
theorem o2 : V.ofConstantList [.splat (.bool true) 2] = [.aggregate [.bool true, .bool true]] := rfl

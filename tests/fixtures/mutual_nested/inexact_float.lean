-- Block 9 (trust-ir Semantics/Step.lean:121): or-patterns and the pair
-- intermediate.
inductive C where
  | int : Int → C
  | float : Nat → C
  | aggregate : List C → C
  | vector : List C → C
  | sequence : List C → C
  | set : List C → C
  | record : List (String × C) → C
  | closure : Nat → List C → C
def isExact (f : Nat) : Bool := f % 2 == 0

mutual
def constHasInexactFloat : C → Bool
  | .float f => !isExact f
  | .aggregate cs | .vector cs | .sequence cs | .set cs => constListHasInexactFloat cs
  | .record fs => constFieldListHasInexactFloat fs
  | .closure _ caps => constListHasInexactFloat caps
  | _ => false
def constListHasInexactFloat : List C → Bool
  | [] => false
  | c :: cs => constHasInexactFloat c || constListHasInexactFloat cs
def constFieldListHasInexactFloat : List (String × C) → Bool
  | [] => false
  | (_, c) :: fs => constHasInexactFloat c || constFieldListHasInexactFloat fs
end
theorem i1 : constHasInexactFloat (.set [.int 1, .record [("x", .float 3)]]) = true := by decide
theorem i2 : constHasInexactFloat (.sequence [.float 2, .closure 0 [.float 4]]) = false := by decide

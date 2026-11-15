-- False twin of inexact_float.lean.
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
theorem i1_twin : constHasInexactFloat (.vector [.record [("x", .float 3)]]) = false := by decide

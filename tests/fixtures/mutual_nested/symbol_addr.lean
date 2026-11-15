-- Block 1 at small closed constants, which Lean 4.8's `decide` reaches.
inductive C where
  | int : Int → C
  | float : Nat → C
  | aggregate : List C → C
  | vector : List C → C
  | record : List (String × C) → C
  | closure : Nat → List C → C
  | symbolAddr : String → Int → C
  | splat : C → Nat → C
  | phantomData : C

mutual
def C.has : C → Bool
  | .symbolAddr _ _ => true
  | .aggregate cs   => C.lhas cs
  | .vector cs      => C.lhas cs
  | .record fs      => C.fhas fs
  | .closure _ caps => C.lhas caps
  | .splat c _      => C.has c
  | .int _          => false
  | .float _        => false
  | .phantomData    => false
def C.lhas : List C → Bool
  | []      => false
  | c :: cs => C.has c || C.lhas cs
def C.fhas : List (String × C) → Bool
  | []           => false
  | (_, c) :: fs => C.has c || C.fhas fs
end
theorem h1 : C.has (.splat (.symbolAddr "x" 0) 2) = true := by decide
theorem h2 : C.fhas [("a", .int 1)] = false := by decide
theorem h3 : C.lhas [.int 1, .symbolAddr "y" 1] = true := by decide

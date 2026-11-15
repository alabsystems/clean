-- False twin of symbol_addr_widening.lean.
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
theorem t1_twin : C.has (.record [("a", .aggregate [.symbolAddr "x" 0])]) = false := by decide

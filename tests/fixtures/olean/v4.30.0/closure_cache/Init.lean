prelude
/-!
A LEAF module for the graduate closure-cache tests: `prelude` means it imports
nothing, so a closure `{Target, Init}` built from it is acyclic. Compiled by the
pinned toolchain; see README.md beside it.
-/
inductive Leaf : Type where
  | mk : Leaf

def Leaf.same (x : Leaf) : Leaf := x

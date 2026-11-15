namespace SectionRelativeBoundary
inductive Tree where
 | leaf : Tree
 | node : Tree → Tree
def Tree.relative (k : Nat) (a : Tree) (n : Tree) : Nat :=
 let z := k
 match n with
 | .leaf => z
 | .node tail => Tree.relative k a tail + 1
theorem useRelative : Tree.relative 3 .leaf (.node .leaf) = 4 := rfl
end SectionRelativeBoundary

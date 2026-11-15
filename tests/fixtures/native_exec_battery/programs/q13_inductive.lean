inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

def Tree.insert : Tree → Nat → Tree
  | .leaf, v => .node .leaf v .leaf
  | .node l x r, v => if v < x then .node (l.insert v) x r else .node l x (r.insert v)

def Tree.toList : Tree → List Nat
  | .leaf => []
  | .node l x r => l.toList ++ [x] ++ r.toList

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

def main : IO Unit := do
  let t := [5, 2, 8, 1, 9, 3].foldl Tree.insert .leaf
  IO.println (toString t.toList)
  IO.println (toString (isEven 10))
  IO.println (toString (isOdd 7))

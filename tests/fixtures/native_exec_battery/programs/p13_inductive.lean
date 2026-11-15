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

def gcd' (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

def main : IO Unit := do
  let t := [5, 2, 8, 1, 9, 3].foldl Tree.insert .leaf
  IO.println t.toList
  IO.println (isEven 10)
  IO.println (isOdd 7)
  IO.println (gcd' 48 18)

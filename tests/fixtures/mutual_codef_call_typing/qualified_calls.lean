mutual
  codata ReviewLeft (A : Type) where
    tag : Nat
    next : ReviewRight A
  codata ReviewRight (A : Type) where
    tag : Nat
    next : ReviewLeft A
end
mutual
  codef ReviewCalls.left (s : Nat) : ReviewLeft Nat where
    tag := 1
    next := ReviewCalls.right s
  codef ReviewCalls.right (s : Nat) : ReviewRight Nat where
    tag := 2
    next := ReviewCalls.left s
end
example : ReviewRight.tag (ReviewLeft.next (ReviewCalls.left 0)) = 2 := rfl

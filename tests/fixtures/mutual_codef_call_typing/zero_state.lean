mutual
  codata ReviewLeft (A : Type) where
    tag : Nat
    next : ReviewRight A
  codata ReviewRight (A : Type) where
    tag : Nat
    next : ReviewLeft A
end
mutual
  codef reviewLeft : ReviewLeft Nat where
    tag := 1
    next := reviewRight
  codef reviewRight : ReviewRight Nat where
    tag := 2
    next := reviewLeft
end
example : ReviewRight.tag (ReviewLeft.next reviewLeft) = 2 := rfl

def ReviewNat : Type := Nat
mutual
  codata ReviewLeft (A : Type) where
    tag : Nat
    next : ReviewRight A
  codata ReviewRight (A : Type) where
    tag : Nat
    next : ReviewLeft A
end
mutual
  codef reviewLeft (s : Nat) : ReviewLeft ReviewNat where
    tag := 1
    next := reviewRight s
  codef reviewRight (s : Nat) : ReviewRight Nat where
    tag := 2
    next := reviewLeft s
end

example : ReviewRight.tag (ReviewLeft.next (reviewLeft 0)) = 2 := rfl

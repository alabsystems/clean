mutual
  codata «Left.dot» (A : Type) where
    tag : Nat
    next : «Right.dot» A
  codata «Right.dot» (A : Type) where
    tag : Nat
    next : «Left.dot» A
end
mutual
  codef «left.fn» (s : Nat) : «Left.dot» Nat where
    tag := 1
    next := «right.fn» s
  codef «right.fn» (s : Nat) : «Right.dot» Nat where
    tag := 2
    next := «left.fn» s
end
example : «Right.dot».tag («Left.dot».next («left.fn» 0)) = 2 := rfl

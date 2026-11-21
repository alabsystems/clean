mutual
  codata GenericLeft (A : Type) where
    tag : A
    next : GenericRight A
  codata GenericRight (A : Type) where
    tag : A
    next : GenericLeft A
end
mutual
  codef genericRight (s : A × Bool) : GenericRight A where
    tag := s.1
    next := genericLeft (s.1, 0)
  codef genericLeft (s : A × Nat) : GenericLeft A where
    tag := s.1
    next := genericRight (s.1, true)
end
example (a : A) : GenericLeft.tag (genericLeft (a, 7)) = a := rfl
example (a : A) : GenericRight.tag (GenericLeft.next (genericLeft (a, 7))) = a := rfl

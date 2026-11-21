mutual
  codata ReviewLeft (A : Type) where
    tag : Nat
    next : ReviewRight A
  codata ReviewRight (A : Type) where
    tag : Nat
    next : ReviewLeft A
end
mutual
  codef reviewLeft (s : _) : ReviewLeft Nat where
    tag := s
    next := reviewRight s
  codef reviewRight (s : _) : ReviewRight Nat where
    tag := s
    next := reviewLeft s
end

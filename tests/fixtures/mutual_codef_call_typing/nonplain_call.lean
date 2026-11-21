mutual
  codata ReviewLeft (A : Type) where
    tag : Nat
    next : ReviewRight A
  codata ReviewRight (A : Type) where
    tag : Nat
    next : ReviewLeft A
end
mutual
  codef reviewLeft (s : Nat) : ReviewLeft Nat where
    tag := 1
    next := (fun x => reviewRight x) s
  codef reviewRight (s : Nat) : ReviewRight Nat where
    tag := 2
    next := reviewLeft s
end

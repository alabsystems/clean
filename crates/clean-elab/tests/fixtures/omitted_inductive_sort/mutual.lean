mutual
inductive Even where
  | zero
  | succ : Odd → Even
inductive Odd where
  | succ : Even → Odd
end
mutual
inductive HighA where
  | mk : Type → HighB → HighA
inductive HighB where
  | mk : HighA → HighB
end

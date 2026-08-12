structure P2.{u, v} (A : Type u) (B : Type v) where
  fst : A
  snd : B
def concrete : P2 Nat Nat := P2.mk Nat.zero Nat.zero

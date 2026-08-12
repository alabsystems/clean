structure P2.{u, v} (A : Type u) (B : Type v) where
  fst : A
  snd : B
def use2.{u, v} {A : Type u} {B : Type v} (a : A) (b : B) : P2 A B :=
  P2.mk a b

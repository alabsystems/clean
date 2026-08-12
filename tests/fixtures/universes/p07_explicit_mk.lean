structure P2.{u, v} (A : Type u) (B : Type v) where
  fst : A
  snd : B
def use.{u, v} {A : Type u} {B : Type v} (a : A) (b : B) : P2 A B :=
  @P2.mk A B a b
def proj.{u, v} {A : Type u} {B : Type v} (p : P2 A B) : A := p.fst

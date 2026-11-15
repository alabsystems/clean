module
prelude
universe u

public inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

public inductive B : Type where
  | t
  | f

def secret : B := B.t

structure ProofOnly : Prop where
  property : Eq secret B.t

inductive DataField : Prop where
  | mk (value : B) (property : Eq secret B.t) : DataField

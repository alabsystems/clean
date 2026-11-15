prelude
universe u v

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

init_quot

inductive B : Type where
  | t
  | f

inductive S : B → Type where
  | mk : (a : B) → S B.t

inductive P : Prop where
  | a
  | b

inductive Pair : Type where
  | mk : B → B → Pair

mutual
  inductive Ev : Type where
    | zero : Ev
    | succ : Od → Ev
  inductive Od : Type where
    | succ : Ev → Od
end

inductive L (α : Type) : Type where
  | nil : L α
  | cons : α → L α → L α

inductive T : Type where
  | node : L T → T

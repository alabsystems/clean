inductive AutoBox (A : Type u) where
  | mk : A → AutoBox A
inductive TypeBox where
  | mk : (A : Type) → TypeBox
inductive Flag where
  | a
  | b
inductive Phantom (A : Type u) where
  | mk
inductive DepBox (A : Type u) (B : A → Type v) where
  | mk : (a : A) → B a → DepBox A B
inductive Tree (A : Type u) where
  | leaf : A → Tree A
  | branch : Tree A → Tree A → Tree A
inductive ListedBox.{u} (A : Type u) where
  | mk : A → ListedBox A
inductive SmallBox (A : Type) : Type where
  | mk : A → SmallBox A
inductive Proposition (A : Type u) : Prop where
  | mk : A → Proposition A

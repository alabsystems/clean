inductive BadBox (A : Type u) : Type where
  | mk : A → BadBox A

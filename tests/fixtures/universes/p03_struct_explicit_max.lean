structure PP.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
  fst : A
  snd : B

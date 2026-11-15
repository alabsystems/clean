import Init.Prelude
def Q2CollisionRose._List : Type := Empty
def q2CollisionElim (e : Q2CollisionRose._List) : False := nomatch e
inductive Q2CollisionRose : Type where
  | mk : List Q2CollisionRose → Q2CollisionRose

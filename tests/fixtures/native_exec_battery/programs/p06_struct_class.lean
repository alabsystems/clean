structure Point where
  x : Int
  y : Int
deriving Repr, BEq

instance : Add Point := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩
instance : ToString Point := ⟨fun p => s!"({p.x}, {p.y})"⟩

class Shape (α : Type) where
  area : α → Nat
  name : String

structure Sq where
  side : Nat
structure Rect where
  w : Nat
  h : Nat

instance : Shape Sq := ⟨fun s => s.side * s.side, "square"⟩
instance : Shape Rect := ⟨fun r => r.w * r.h, "rect"⟩

def describe {α} [Shape α] (x : α) : String :=
  s!"{Shape.name α}: {Shape.area x}"

def main : IO Unit := do
  let p : Point := ⟨1, -2⟩
  let q : Point := ⟨3, 4⟩
  IO.println (toString (p + q))
  IO.println (p == q)
  IO.println (repr p)
  IO.println (describe (Sq.mk 3))
  IO.println (describe (Rect.mk 2 5))

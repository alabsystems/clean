-- Accepted with no message: `lean` prints nothing and exits 0.
def x : Nat := 1

theorem x_eq : x = 1 := rfl

structure Point where
  x : Nat
  y : Nat

def Point.sum (p : Point) : Nat := p.x + p.y

example : Point.sum ⟨1, 2⟩ = 3 := rfl

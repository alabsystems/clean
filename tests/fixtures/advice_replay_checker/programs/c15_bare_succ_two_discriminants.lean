inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

namespace Tm

def same : Tm → Tm → Bool
  | lit m, lit n => m == n
  | succ a, succ b => same a b
  | _, _ => false

end Tm

def main : IO Unit := do
  IO.println (toString (Tm.same (.succ (.succ (.lit 1))) (.succ (.succ (.lit 1)))))
  IO.println (toString (Tm.same (.succ (.succ (.lit 1))) (.succ (.succ (.lit 2)))))
  IO.println (toString (Tm.same (.succ (.lit 1)) (.lit 1)))

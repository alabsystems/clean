-- NEGATIVE CONTROL for frontend class (197): inside `namespace Tm` a bare
-- `succ` head is `Tm.succ`, so over a `Nat` column pinned Lean rejects it.
-- Reading the head by the column's type instead would accept `Nat.succ`.
inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

namespace Tm

def bad : Nat → Nat → Nat
  | succ n, succ _ => n
  | _, _ => 0

end Tm

def main : IO Unit :=
  IO.println s!"{Tm.bad 5 3}"

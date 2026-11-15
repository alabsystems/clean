-- Outside `namespace Tm` a bare `succ` is not `Tm.succ`: pinned Lean rejects
-- the pattern ("Invalid pattern"). Clean reads the head against the column's
-- type and accepts it; that acceptance predates frontend class (197) and is
-- tracked as an open false acceptance.
inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

def bad : Tm → Tm → Nat
  | succ _, succ _ => 1
  | _, _ => 0

def main : IO Unit :=
  IO.println s!"{bad (.succ (.lit 0)) (.succ (.lit 1))}"

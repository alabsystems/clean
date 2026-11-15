inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm

namespace Tm

def size : Tm → Nat
  | var _ => 1
  | app f a => size f + size a + 1
  | lam b => size b + 1

end Tm

def main : IO Unit :=
  IO.println (toString (Tm.size (.lam (.app (.var 0) (.var 1)))))

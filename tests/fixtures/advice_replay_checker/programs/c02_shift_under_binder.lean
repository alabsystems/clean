inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm

def Tm.shift (d : Nat) : Nat → Tm → Tm
  | c, .var i => if i < c then .var i else .var (i + d)
  | c, .app f a => .app (Tm.shift d c f) (Tm.shift d c a)
  | c, .lam b => .lam (Tm.shift d (c + 1) b)

def Tm.render : Tm → String
  | .var i => "#" ++ toString i
  | .app f a => "(" ++ Tm.render f ++ " " ++ Tm.render a ++ ")"
  | .lam b => "(fun " ++ Tm.render b ++ ")"

def main : IO Unit :=
  IO.println (Tm.render (Tm.shift 2 0 (.lam (.app (.var 0) (.lam (.app (.var 1) (.var 2)))))))

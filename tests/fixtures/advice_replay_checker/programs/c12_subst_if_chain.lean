inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm

def Tm.subst (s : Tm) : Nat → Tm → Tm
  | k, .var i =>
    if i < k then .var i
    else if i == k then s
    else .var (i - 1)
  | k, .app f a => .app (Tm.subst s k f) (Tm.subst s k a)
  | k, .lam b => .lam (Tm.subst s (k + 1) b)

def Tm.render : Tm → String
  | .var i => "#" ++ toString i
  | .app f a => "(" ++ Tm.render f ++ " " ++ Tm.render a ++ ")"
  | .lam b => "(fun " ++ Tm.render b ++ ")"

def main : IO Unit :=
  IO.println (Tm.render (Tm.subst (.var 7) 0 (.app (.var 0) (.lam (.app (.var 1) (.app (.var 0) (.var 2)))))))

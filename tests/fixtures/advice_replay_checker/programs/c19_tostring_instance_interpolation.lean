inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm

def Tm.render : Tm → String
  | .var i => s!"#{i}"
  | .app f a => s!"({Tm.render f} {Tm.render a})"

instance : ToString Tm := ⟨Tm.render⟩

def main : IO Unit := do
  let t := Tm.app (.var 0) (.app (.var 1) (.var 2))
  IO.println s!"term {t} has {3} leaves"

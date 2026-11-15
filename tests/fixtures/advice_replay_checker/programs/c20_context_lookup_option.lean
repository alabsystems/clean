def lookup (ctx : List String) (i : Nat) : Except String String :=
  match ctx[i]? with
  | some ty => .ok ty
  | none => .error s!"variable #{i} is out of scope"

def show' : Except String String → String
  | .ok v => "ok " ++ v
  | .error e => "error " ++ e

def main : IO Unit := do
  IO.println (show' (lookup ["Nat", "Bool", "Prop"] 1))
  IO.println (show' (lookup ["Nat", "Bool", "Prop"] 3))

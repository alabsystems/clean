inductive Rule where
  | beta
  | addLit

structure Step where
  path : List Nat
  rule : Rule

structure Case where
  name : String
  fuel : Nat
  advice : List Step

def Rule.name : Rule → String
  | .beta => "beta"
  | .addLit => "addLit"

def describe (c : Case) : String :=
  c.name ++ " fuel=" ++ toString c.fuel ++ " steps=" ++ toString c.advice.length

def cases : List Case :=
  [ { name := "one", fuel := 8, advice := [⟨[], .beta⟩] },
    { name := "two", fuel := 3, advice := [⟨[0, 1], .addLit⟩, ⟨[], .beta⟩] },
    { name := "none", fuel := 0, advice := [] } ]

def firstRule (c : Case) : String :=
  match c.advice with
  | [] => "-"
  | s :: _ => s.rule.name ++ "@" ++ toString s.path.length

def main : IO Unit := do
  IO.println (toString (cases.map describe))
  IO.println (toString (cases.map firstRule))

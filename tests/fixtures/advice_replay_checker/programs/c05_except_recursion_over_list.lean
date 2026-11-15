inductive Dir where
  | fn
  | arg

inductive Tm where
  | lit : Nat → Tm
  | app : Tm → Tm → Tm

def get : List Dir → Tm → Except String Nat
  | [], .lit n => .ok n
  | [], _ => .error "not a literal"
  | .fn :: rest, .app f _ => do
    let n ← get rest f
    pure (n + 1)
  | .arg :: rest, .app _ a => do
    let n ← get rest a
    pure (n + 100)
  | _ :: _, _ => .error "path leaves the term"

def show' : Except String Nat → String
  | .ok v => "ok " ++ toString v
  | .error e => "error " ++ e

def main : IO Unit := do
  IO.println (show' (get [.fn, .arg] (.app (.app (.lit 1) (.lit 2)) (.lit 3))))
  IO.println (show' (get [.fn] (.app (.app (.lit 1) (.lit 2)) (.lit 3))))
  IO.println (show' (get [.arg, .arg] (.app (.app (.lit 1) (.lit 2)) (.lit 3))))

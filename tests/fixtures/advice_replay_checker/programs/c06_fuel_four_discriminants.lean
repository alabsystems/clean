def replay : Nat → Nat → List Nat → Nat → Except Nat Nat
  | _, _, [], t => .ok t
  | 0, idx, _ :: _, _ => .error idx
  | fuel + 1, idx, s :: rest, t => do
    let t' ← (if s == 0 then Except.error idx else Except.ok (t + s))
    replay fuel (idx + 1) rest t'

def show' : Except Nat Nat → String
  | .ok v => "ok " ++ toString v
  | .error e => "error at " ++ toString e

def main : IO Unit := do
  IO.println (show' (replay 8 0 [1, 2, 3] 10))
  IO.println (show' (replay 2 0 [1, 2, 3] 10))
  IO.println (show' (replay 8 0 [1, 0, 3] 10))
  IO.println (show' (replay 0 0 [] 10))

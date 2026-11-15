def work (n : Nat) : Nat := (List.range n).foldl (· + ·) 0

def main : IO Unit := do
  let t1 := Task.spawn fun _ => work 1000
  let t2 := Task.spawn fun _ => work 2000
  IO.println (t1.get + t2.get)
  let t3 ← IO.asTask (do IO.println "in task"; return 7)
  match ← IO.wait t3 with
  | .ok v => IO.println v
  | .error e => IO.println s!"err {e}"

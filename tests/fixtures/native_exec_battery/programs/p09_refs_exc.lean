def mayFail (n : Nat) : IO Nat := do
  if n == 0 then throw (IO.userError "zero!")
  return 100 / n

def main : IO Unit := do
  let r ← IO.mkRef 0
  for i in [1, 2, 3] do
    r.modify (· + i)
  IO.println (← r.get)
  try
    let v ← mayFail 4
    IO.println v
    let w ← mayFail 0
    IO.println w
  catch e =>
    IO.println s!"caught: {e}"
  let out ← IO.getStdout
  out.putStrLn "via stdout handle"

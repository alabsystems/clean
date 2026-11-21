import Source

def main (args : List String) : IO Unit := do
  let n := (args.headD "0").toNat!
  for value in [runLeft n, runRight n, runPair n, runFunctionLeft n,
      runFunctionRight n, runLambdaLong n, runNone n] do
    IO.println value

def main : IO Unit := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  IO.println s!"got: {line.trim}"

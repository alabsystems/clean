def main : IO Unit := do
  let acts := ["a", "b"].map IO.println
  IO.println "done"

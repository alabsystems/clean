def main : IO Unit := do
  let a := #[1, 2]
  IO.println (a[5]!)
  IO.println "after"

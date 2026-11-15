def main : IO Unit := do
  let a : Array Nat := #[1, 2]
  IO.println (toString (a[5]!))
  IO.println "after"

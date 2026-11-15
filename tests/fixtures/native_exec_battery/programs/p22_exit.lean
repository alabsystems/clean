def main : IO Unit := do
  IO.println "before exit"
  IO.Process.exit 7

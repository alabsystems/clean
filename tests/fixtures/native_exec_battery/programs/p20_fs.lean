def main : IO Unit := do
  let p : System.FilePath := "clean_audit_fs_test.txt"
  IO.FS.writeFile p "line1\nline2\n"
  let c ← IO.FS.readFile p
  IO.print c
  let ls ← IO.FS.lines p
  IO.println ls.size
  IO.FS.removeFile p
  IO.println (← p.pathExists)

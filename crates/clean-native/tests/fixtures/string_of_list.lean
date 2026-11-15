def main (args : List String) : IO Unit := do
  let n := args.length
  let xs : List Char :=
    [Char.ofNat (97 + n), Char.ofNat 0, Char.ofNat 233,
     Char.ofNat 8364, Char.ofNat (128512 + n)]
  let s := String.ofList xs
  IO.println s
  IO.println s
  IO.println (String.ofList [])

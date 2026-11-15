
def emit (s : String) : IO Unit := do
  let t := String.append (String.append s (toString (Char.ofNat 0))) "β\x007"
  IO.print "a\x00b"
  IO.println t
  IO.println t
  IO.println (@ToString.toString Nat { toString := fun _ => t } 5)
  IO.println (String.append t t)
  IO.println (toString (Char.ofNat s.length))
  IO.println (String.append (String.append t (toString (Char.ofNat 233))) (toString (Char.ofNat 8364)))
  let c := Char.ofNat (s.length + 128512)
  IO.println (String.append t (toString c))
  IO.println (toString c)
  IO.println (toString t.length)
  IO.println "\x00\x00"
  IO.println ""
  IO.eprintln t
def main (args : List String) : IO Unit :=
  match args with
  | [] => emit ""
  | s :: _ => emit s

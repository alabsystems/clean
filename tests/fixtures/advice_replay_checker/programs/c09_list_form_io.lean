def lines : List String := ["a: 1", "b: 2", "c: 3"]

def main : IO Unit :=
  lines.forM fun l => IO.println l

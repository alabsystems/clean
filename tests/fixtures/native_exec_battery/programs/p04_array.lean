def main : IO Unit := do
  let a := #[5, 3, 8, 1, 9, 2]
  IO.println a
  IO.println (a.push 7)
  IO.println a.size
  IO.println (a.map (· * 2))
  IO.println (a.foldl (· + ·) 0)
  IO.println a[2]!
  IO.println (Array.range 5)
  IO.println (a.qsort (· < ·))
  IO.println (a.toList)
  IO.println (a.contains 8)
  let mut b : Array Nat := #[]
  for i in [0:5] do
    b := b.push (i * i)
  IO.println b
  IO.println (a.filter (· % 2 == 0))
  IO.println (a.reverse)

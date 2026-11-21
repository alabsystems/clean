/-!
X4 regression: `for` loops in `IO` whose state is `PUnit`. Each loop's
continuation calls the loop function directly with the `PUnit` state it
projects out of `ForInStep.yield`: an object passed to a parameter that Clean
erases. Before the post-boxing repair released it
(`rc_repair::release_consuming_unboxes`), the RC linearity check refused the
program (`object %5 is consumed 0 times with 1 incs`).
-/

def main : IO Unit := do
  for c in [1, 2, 3] do
    IO.println (toString c)
  for s in ["a", "b"] do
    IO.println s

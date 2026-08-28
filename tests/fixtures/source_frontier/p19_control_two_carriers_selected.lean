-- p19 — CLASS I risk axis (a): over-eager candidate admission.
--
-- PROVES: with TWO `def`-based alias locals in scope at DIFFERENT carriers,
-- each `Decidable` sub-goal takes its OWN dictionary. The candidate-side
-- match scans locals innermost-first, so a sloppy implementation that grabs
-- the first local it can name would answer the `α` sub-goal with the `β`
-- binder; the elaborated term would then be ill-typed and the KERNEL, which
-- re-checks every emitted term exactly as before, would reject it.
--
-- So this file passing is evidence of SELECTION, not merely of admission:
-- both `if`s elaborate and both survive the kernel.
--
-- CONTROL PAIR: p20 — the same shape with NO matching local must still FAIL.
-- p19 without p20 would be satisfied by "grab any local"; p20 without p19
-- would be satisfied by "grab nothing". Together they pin the boundary.
def twoCarriers {α β : Type} [DecidableEq α] [DecidableEq β] (a : α) (b : β) : Bool :=
  if a = a then (if b = b then true else false) else false

-- p12 — CLASS I CONTROL (PASS). The term side is fine; only lookup is broken.
--
-- PROVES: the very same `DecidableEq α` value, passed as an ORDINARY explicit
-- argument rather than synthesised, elaborates and kernel-checks. The binder
-- `[d : DecidableEq α]` is a perfectly good local of a perfectly good type.
--
-- RULES OUT: "`DecidableEq` is somehow not a usable type in Clean", and
-- "the `def`-based alias breaks unification/elaboration generally". It breaks
-- exactly one thing: INSTANCE SEARCH's ability to recognise it, on the goal
-- side (p09) and on the candidate side (p11).
def callee3 {α : Type} (d : DecidableEq α) (a : α) : Nat := 0

theorem probe_explicit {α : Type} [d : DecidableEq α] (a : α) : callee3 d a = 0 := rfl

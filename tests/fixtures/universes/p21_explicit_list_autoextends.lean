-- KNOWN Lean divergence (rung-4 scope cut, 2026-08-09): Lean treats an
-- explicit `.{...}` list as CLOSED (a leaked fresh level errors); Clean
-- auto-extends, because the file-context preprocessor folds `universe u`
-- names into the same list and the two are indistinguishable at decl
-- close. This pin documents the divergence: leak generalizes to arity 2.
def leak.{u} (A : Type u) (a : A) := fun (B : Type _) (b : B) => b

def useLeak : Nat := @leak.{0, 0} Nat Nat.zero Nat Nat.zero

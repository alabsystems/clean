-- P32 — legitimate universe polymorphism inside `mutual` still works.
--
-- The p31 fix makes declared universes rigid on the mutual path. This probe
-- pins that rigidity did not become over-strict: a genuinely polymorphic
-- mutual definition still elaborates AND still accepts an explicit universe
-- argument, so the parameter really survived rather than being dropped.
mutual
  def idm.{u} {A : Sort u} (a : A) : A := a
end

def useIdm : Nat := @idm.{1} Nat Nat.zero

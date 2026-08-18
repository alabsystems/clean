-- P34 — the CONTROL that bounds p33: `structure ... extends` at the same
-- universes WORKS.
--
-- Structures do not synthesise a derived parent instance; classes do. That is
-- the whole difference, and it is why the fix is local to the class path rather
-- than a universe-solver problem. Keeping this pinned means a future fix cannot
-- "succeed" by breaking the structure path instead.
structure P34A (α : Type u) where
  car : α

structure P34B (α : Type u) extends P34A α where
  tag : Nat

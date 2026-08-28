-- p23 — CLASS I, the general capability, with the `decEq` bridge removed from
-- the picture.
--
-- PROVES: `infer/instance.rs` carries a hand-written bridge for exactly one
-- shape — `Decidable (@Eq α a b)` delegating to `DecidableEq α`. p08 and p09
-- both run through it, so on their own they cannot distinguish "the bridge
-- now reaches its dictionary" from "local instances are telescoped".
--
-- This file uses a user-declared class and a user-declared `def`-based alias
-- that the bridge has never heard of: `MyDEq α := (x y : α) → MyD (x = y)`.
-- The goal `MyD (a = b)` is answered by opening the local's ∀-telescope,
-- unifying its conclusion against the goal, and returning `h a b` — the local
-- APPLIED, not the bare binder. Nothing else in the tree can produce that
-- term.
--
-- CONTROL: p22 — the same machinery over a local whose conclusion leaves a
-- binder undetermined is refused. So this pass is a determined match, not a
-- blanket admission of any Pi-shaped local.
class MyD (p : Prop) where
  ev : Nat

def MyDEq (α : Type) : Type := (x : α) → (y : α) → MyD (x = y)

def evAt (p : Prop) [MyD p] : Nat := MyD.ev

def usesTelescope {α : Type} [MyDEq α] (a b : α) : Nat := evAt (a = b)

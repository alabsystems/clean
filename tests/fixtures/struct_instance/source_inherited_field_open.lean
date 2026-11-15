-- THE BOUNDARY of bricks 12 and 18, pinned as a NEGATIVE so it cannot be
-- mistaken for covered: an explicitly-assigned INHERITED field alongside a
-- source whose structure is not the target's.
--
-- Lean accepts both declarations below (measured, pinned `lean` v4.30.0-rc2,
-- the second with the real Mathlib checkout on `LEAN_PATH`,
-- `set_option pp.parens true`):
--
--     def openWith : Base3 → Deriv3 :=
--     fun s => { b := 1, c := s.c, d := 7 }
--
--     def openSpread : Deriv3 → Deriv3 :=
--     fun x => (have __spread.0 := x;
--               { b := 1, c := __spread.0.c, d := __spread.0.d })
--
-- (Lean prints the FLAT constructor here — it fills each flattened field from
-- the source and re-compacts with `etaStructReduce'`, which is exactly why the
-- shape is free for Lean and is a routing step for Clean.)
--
-- Clean rejects both today. It is NOT a regression from bricks 12/18 — before
-- them, `openWith` failed as `Unknown structure field d on Base3` (it decided
-- it was building a `Base3`) and `openSpread` failed as
-- `Unknown structure field __ on Deriv3`. What is left is one missing step:
-- Clean stores an `extends` parent as a NESTED subobject, so an inherited field
-- assignment has to be routed into the `toBase3` slot, and that slot's OTHER
-- fields then have to come from the source. `rewrite_inherited_field_updates`
-- does exactly that routing, but it can only do it by projecting `base.toBase3`
-- out of the source in surface syntax, which exists only when the source IS the
-- target structure. Building the slot from a source of a different structure
-- needs the parent's own constructor telescope, i.e. a second entry into
-- `elab_struct_lit` on an already-elaborated value — there is no `SurfaceExpr`
-- that carries one.
--
-- Mathlib's 1,541 `__ :=` sites do not need this: in the seven in the pinned
-- slice (all `Mathlib/Order/Basic.lean`) every explicitly-assigned field is a
-- field of the structure being built, never an inherited one.

structure Base3 where
  b : Nat
  c : Nat

structure Deriv3 extends Base3 where
  d : Nat

def openWith (s : Base3) : Deriv3 := { s with b := 1, d := 7 }

def openSpread (x : Deriv3) : Deriv3 where
  __ := x
  b := 1

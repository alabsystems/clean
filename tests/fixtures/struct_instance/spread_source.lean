-- Brick 18 (queue-C): `__ := e` in structure-instance notation is a SPREAD —
-- it contributes `e` as an additional `with`-SOURCE.
--
-- CORRECTION TO THE BRICK QUEUE. The queue calls `__ :=` "Lean's
-- parent-structure injection in structure-instance notation". It is neither
-- Lean's nor an injection:
--
--  * It is MATHLIB's, from `Mathlib/Tactic/Spread.lean` ("Macro for spread
--    syntax (`__ := instSomething`) in structures"). The pinned bare
--    `lean` v4.30.0-rc2 rejects it — measured, verbatim:
--        error: `__` is not a field of structure `Deriv2`
--        error: Fields missing: `b`
--    Lean core declares no `__` field syntax and uses none; `normalizeField`
--    (`src/Lean/Elab/StructInst.lean:473`) reports it as an unknown field.
--
--  * It expands to a `with`-source, not to a parent-field assignment:
--        `{ $srcs,* with $fields }` with a `__ := e` field
--          ⇝ `let_impl_detail __spread.0 := e; { $srcs, __spread.0 with $fields }`
--    so a spread fills EVERY field it can provide, exactly like `with`.
--
-- Ground truth below is from the pinned `lean` v4.30.0-rc2 with the real
-- Mathlib checkout on `LEAN_PATH` (`Mathlib/Tactic/Spread.olean`) and
-- `set_option pp.parens true`.

structure Base2 where
  b : Nat
  c : Nat

structure Deriv2 extends Base2 where
  d : Nat

-- THE BRICK, `where` form — this is `Function.Injective.partialOrder`'s shape
-- (`Mathlib/Order/Basic.lean:684`, `__ := Function.Injective.preorder f le lt`).
--
--   def mkD2 : Base2 → Deriv2 :=
--   fun s => (have __spread.0 := s; { toBase2 := __spread.0, d := 7 })
def mkD2 (s : Base2) : Deriv2 where
  __ := s
  d := 7

-- THE BRICK, brace form. Lean prints the identical term.
def mkD2Brace (s : Base2) : Deriv2 := { __ := s, d := 7 }

-- THE ARM THAT REFUTES "parent injection". The spread is the SAME structure as
-- the target and no parent is involved at all, so the only way `q` gets a value
-- is if `__ :=` made `x` a SOURCE:
--
--   def bumpP : Pair → Pair :=
--   fun x => (have __spread.0 := x; { p := 1, q := __spread.0.q })
structure Pair where
  p : Nat
  q : Nat

def bumpP (x : Pair) : Pair where
  __ := x
  p := 1

-- CONTROL: an explicit `with` is the same mechanism, and an explicitly-assigned
-- field always beats a source.
--
--   def mkD2WithBeatsSpread : Base2 → Deriv2 := fun s => { toBase2 := s, d := 7 }
def mkD2WithBeatsSpread (s : Base2) : Deriv2 := { s with d := 7 }

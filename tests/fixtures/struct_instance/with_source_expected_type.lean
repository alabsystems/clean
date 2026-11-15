-- Brick 12 (queue-C): `{ src with f := v }` resolves its fields against the
-- EXPECTED type, not against `src`'s type.
--
-- Ground truth, pinned `lean` v4.30.0-rc2 with `set_option pp.parens true`:
--
--     def mkD : Base → Deriv :=
--     fun s => { toBase := s, d := 7 }
--
-- i.e. Lean builds a `Deriv`, takes `d` from the literal and the whole `toBase`
-- subobject from the source. `getStructName` (`src/Lean/Elab/StructInst.lean`):
-- "If the expected type is available and it is a structure, then we use it.
--  Otherwise, we use the type of the first source."

structure Base where
  b : Nat
  c : Nat

structure Deriv extends Base where
  d : Nat

-- THE BRICK. Source `Base`, expected `Deriv`.
def mkD (s : Base) : Deriv := { s with d := 7 }

-- CONTROL that distinguishes this from a general structure-instance failure:
-- naming the parent subobject explicitly always worked and must keep working.
def mkDExplicitParent (s : Base) : Deriv := { toBase := s, d := 7 }

-- CONTROL: source and expected are the SAME structure — the plain update path,
-- which resolves positionally and is untouched by the brick.
def bumpD (x : Deriv) : Deriv := { x with d := 9 }

-- Source is a strict DESCENDANT of the expected type: the missing field is
-- found by NAME through the source's own parent chain.
def downD (x : Deriv) : Base := { x with c := 5 }

-- U2 rung-6 lift wall, FIXED same day (2026-08-08): the parser bound a
-- `.{levels}` postfix in argument position to the application HEAD
-- (`@f PUnit.{u+1} x` parsed as `f.{u+1} PUnit x`, silently re-leveling
-- the function — every downstream level then off by exactly one). Now
-- `.{}` attaches to the immediately preceding atom, like projection.
def f.{w} {I : Type w} (x : I) : I := x
def t1.{u} : PUnit.{u+1} := @f PUnit.{u+1} PUnit.unit

-- Refuter finding, fixed same day: the closing-brace span was captured
-- AFTER expect() advanced, so the over-extended span defeated byte-
-- adjacency for any postfix after `.{…}` — `X.{u}.ty` misparsed `.ty`
-- as a leading-dot argument. Projection now attaches through.
structure W.{u} where
  ty : Type u

def X.{u} : W.{u+1} := W.mk (Type u)

def viaParen.{u} : Type (u+1) := (X.{u}).ty
def viaAdjacent.{u} : Type (u+1) := X.{u}.ty

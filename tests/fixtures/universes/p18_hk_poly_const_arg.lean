-- The last HK wall, FIXED 2026-08-09: not a unifier bug — the builtin
-- prelude declared Option's TYPE FORMER with an implicit parameter
-- ({α : Sort u} → Sort u), so a bare `Option` in functor position
-- auto-inserted a hole (`Option ?m` : Type ?u) and shape-bailed
-- against `Type → Type`. Lean parity: `Option : Type u → Type u`
-- explicit; ctor params stay implicit.
def apF (E : Type → Type) (X : Type) : Type := E X
def useNamed : Type := apF Option Nat

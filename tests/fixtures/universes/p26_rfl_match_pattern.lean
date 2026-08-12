-- Lean's `@[match_pattern] def rfl` (Init/Prelude.lean:352) in PATTERN
-- position: an alias for the zero-field `Eq.refl` constructor, never a
-- binder (verified against Lean 4.33.0, where `match (n : Nat) with
-- | rfl => 0` is a type error). Parser-only change, three sites in
-- expr_match.rs; `rfl` lexes as a keyword token so no bare-ident
-- variable-pattern behavior could be lost. HEq keeps needing HEq.refl,
-- exactly as in Lean.
theorem symm1 {A : Type} {a b : A} (h : Eq a b) : Eq b a := match h with | rfl => rfl
theorem symm2 {A : Type} {a b : A} (h : a = b) : b = a := match h with | rfl => rfl
def opt1 (o : Option Nat) : Nat := match o with | Option.some n => n | Option.none => 0

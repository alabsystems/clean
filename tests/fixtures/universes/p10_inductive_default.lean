-- U2 rung 5 (flipped 2026-08-08): a `.{u}`-declared inductive with an
-- OMITTED result sort infers it from the constructor fields (Lean's
-- inferResultingUniverse minimality) instead of collapsing to Type 0.
-- Monomorphic inductives keep the concrete-Type default untouched.
inductive Box.{u} (A : Type u) where
  | mk : A → Box A

def bx : Box Nat := Box.mk Nat.zero
def bigBx : Box.{1} Type := Box.mk Nat

inductive Pair2.{u, v} (A : Type u) (B : Type v) where
  | mk : A → B → Pair2 A B

def pr : Pair2 Nat Nat := Pair2.mk Nat.zero Nat.zero

inductive Enum2.{u} where
  | a
  | b

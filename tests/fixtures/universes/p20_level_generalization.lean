-- U2 rung 4 (levelMVarToParam analog, landed 2026-08-09): leftover
-- fresh levels at decl close generalize into a CONTIGUOUS declared
-- tail in first-use order (the old behavior kept mint-index gaps);
-- the @-arity pins prove the exact param count and order.
def id1 := fun (A : Type _) (a : A) => a
def useId1a : Nat := id1 Nat Nat.zero
def useId1b : Type 1 := id1 (Type 1) (Type 0)

def two := fun (A : Type _) (B : Type _) (a : A) (b : B) => a
def useTwo : Nat := @two.{0, 0} Nat Nat Nat.zero Nat.zero

def gap := fun (A : Type _) (n : Nat) (B : Type _) (a : A) (b : B) => a
def useGap : Nat := @gap.{0, 0} Nat Nat.zero Nat Nat.zero Nat.zero

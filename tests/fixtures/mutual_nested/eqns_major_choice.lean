-- Gap G23 brick B3 (judge k5 a1, a2): `simp [f]` with `ty` open; a1 needs the
-- equations of recursion on `c` (block 10, Step.lean:143), not on `ty`.
inductive Ty where
  | I64 : Ty
  | Tuple : List Ty → Ty
  | Vector : Nat → Ty → Ty
inductive C where
  | int : Int → C
  | float : Nat → C
  | aggregate : List C → C
  | vector : List C → C
  | record : List (String × C) → C
def anyFloat : List C → Bool := fun _ => false
def hasFloat : C → Bool := fun _ => false
mutual
def constWidthAmbiguous (ty : Ty) (c : C) : Bool :=
  match c with
  | .float _ => false
  | .aggregate cs =>
    match ty with
    | .Tuple tys =>
      if tys.length == cs.length then constFieldsAmbiguous tys cs
      else anyFloat cs
    | _ => anyFloat cs
  | .vector cs =>
    match ty with
    | .Vector _ _ => false
    | _ => anyFloat cs
  | c => hasFloat c
def constFieldsAmbiguous : List Ty → List C → Bool
  | t :: ts, c :: cs => constWidthAmbiguous t c || constFieldsAmbiguous ts cs
  | _, cs => anyFloat cs
end
theorem a1 (ty : Ty) (n : Nat) : constWidthAmbiguous ty (.float n) = false := by simp [constWidthAmbiguous]
theorem a2 (t : Ty) (ts : List Ty) (c : C) (cs : List C) :
    constFieldsAmbiguous (t :: ts) (c :: cs) = (constWidthAmbiguous t c || constFieldsAmbiguous ts cs) := by
  simp [constFieldsAmbiguous]

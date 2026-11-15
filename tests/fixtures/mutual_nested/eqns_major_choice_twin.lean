-- Twin of eqns_major_choice.lean a1.
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
theorem a1f (ty : Ty) (n : Nat) : constWidthAmbiguous ty (.float n) = true := by simp [constWidthAmbiguous]

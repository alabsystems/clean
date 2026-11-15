import Init.Prelude
universe u
inductive Q2ParamUnit (α : Sort u) : Type where
  | mk : Q2ParamUnit α
inductive Q2DataBox : Type where
  | mk (value : Nat) : Q2DataBox

theorem q2UnitNeutral (x y : Unit) : x = y := rfl
theorem q2PUnitNeutral (x y : PUnit.{u}) : x = y := rfl
theorem q2ParamUnitNeutral {α : Sort u} (x y : Q2ParamUnit α) : x = y := rfl

def Q2ConstType (x _y : Type) : Type := x
set_option genSizeOf false in
inductive Q2ReducedField (α : Type) : Type where
  | leaf : Q2ReducedField α
  | mk : Q2ConstType (Q2ReducedField α) (Q2ReducedField α) → Q2ReducedField α

noncomputable def q2ReducedFold {α : Type} : Q2ReducedField α → Nat :=
  Q2ReducedField.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.succ ih)
theorem q2ReducedIota {α : Type} (x : Q2ReducedField α) :
    q2ReducedFold (.mk x) = Nat.succ (q2ReducedFold x) := rfl

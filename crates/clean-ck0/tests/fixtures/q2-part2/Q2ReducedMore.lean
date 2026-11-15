import Init.Prelude
set_option genSizeOf false

def Q2ReducedSelect (x _y : Type) : Type := x
mutual
  inductive Q2ReducedA (α : Type) : Type where
    | leaf : Q2ReducedA α
    | step : Q2ReducedSelect (Q2ReducedB α) (Q2ReducedB α) → Q2ReducedA α
  inductive Q2ReducedB (α : Type) : Type where
    | leaf : Q2ReducedB α
    | step : Q2ReducedSelect (Q2ReducedA α) (Q2ReducedA α) → Q2ReducedB α
end
inductive Q2ReducedReflexive : Type where
  | leaf : Q2ReducedReflexive
  | step : Q2ReducedSelect (Unit → Q2ReducedReflexive) (Unit → Q2ReducedReflexive) → Q2ReducedReflexive
noncomputable def q2ReducedReflexiveFold : Q2ReducedReflexive → Nat :=
  Q2ReducedReflexive.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.succ (ih ()))
theorem q2ReducedReflexiveIota (f : Unit → Q2ReducedReflexive) :
    q2ReducedReflexiveFold (.step f) = Nat.succ (q2ReducedReflexiveFold (f ())) := rfl

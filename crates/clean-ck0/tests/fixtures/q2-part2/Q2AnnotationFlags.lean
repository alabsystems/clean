import Init.Prelude
set_option genSizeOf false
inductive Q2AnnotatedField : Type where
  | leaf
  | step : outParam (Unit → Q2AnnotatedField) → Q2AnnotatedField
noncomputable def q2AnnotatedFold : Q2AnnotatedField → Nat :=
  Q2AnnotatedField.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.succ (ih ()))
theorem q2AnnotatedIota (f : Unit → Q2AnnotatedField) :
    q2AnnotatedFold (.step f) = Nat.succ (q2AnnotatedFold (f ())) := rfl
def q2IgnoredType (_α : Type) : Nat := 0
inductive Q2AnnotatedEta : Type where
  | mk (n : optParam Nat (q2IgnoredType Q2AnnotatedEta))
noncomputable def q2AnnotatedValue : Q2AnnotatedEta → Nat :=
  Q2AnnotatedEta.rec (motive := fun _ => Nat) (fun n => n)
theorem q2AnnotatedEtaEq (x : Q2AnnotatedEta) : x = .mk (q2AnnotatedValue x) := by
  fail_if_success exact Eq.refl x
  cases x
  rfl

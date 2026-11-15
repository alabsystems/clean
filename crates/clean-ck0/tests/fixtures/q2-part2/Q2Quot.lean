import Init.Prelude
universe u
inductive Q2FakeEq (α : Sort u) (a : α) : α → Prop where
  | refl (b : α) : Q2FakeEq α a b

def q2QuotRelation (_ _ : Nat) : Prop := True
def q2QuotValue (n : Nat) : Quot q2QuotRelation := Quot.mk q2QuotRelation n
def q2QuotLift (n : Nat) : Nat :=
  Quot.lift (fun _ : Nat => 0) (fun _ _ _ => rfl) (q2QuotValue n)
theorem q2QuotLiftIota (n : Nat) : q2QuotLift n = 0 := rfl

theorem q2QuotIndProof (n : Nat) : True :=
  @Quot.ind Nat q2QuotRelation (fun _ => True) (fun _ => True.intro) (q2QuotValue n)

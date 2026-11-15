import Init.Prelude
universe u
inductive Q2Rose (α : Type u) : Type u where
  | node : α → List (Q2Rose α) → Q2Rose α
inductive Q2ArrayRose : Type where
  | node : Array Q2ArrayRose → Q2ArrayRose
inductive Q2FunctionRose : Type where
  | node : (Nat → List Q2FunctionRose) → Q2FunctionRose
#print Q2Rose.rec
#print Q2ArrayRose.rec

theorem q2ListNestedIota :
    @Q2Rose.rec Nat (fun _ => Nat) (fun _ => Nat)
      (fun _ _ ih => Nat.succ ih)
      0 (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂)
      (Q2Rose.node 0 [Q2Rose.node 1 []]) = 2 := rfl

theorem q2ArrayNestedIota :
    @Q2ArrayRose.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
      (fun _ ih => Nat.succ ih) (fun _ ih => ih)
      0 (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂)
      (Q2ArrayRose.node #[Q2ArrayRose.node #[]]) = 2 := rfl

theorem q2FunctionNestedIota :
    @Q2FunctionRose.rec (fun _ => Nat) (fun _ => Nat)
      (fun _ ih => Nat.succ (ih 0))
      0 (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂)
      (Q2FunctionRose.node (fun _ => [])) = 1 := rfl

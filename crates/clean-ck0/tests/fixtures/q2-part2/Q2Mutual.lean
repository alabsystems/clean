import Init.Prelude
universe u
mutual
  inductive Q2Tree (α : Type u) : Type u where
    | node : Q2Forest α → Q2Tree α
  inductive Q2Forest (α : Type u) : Type u where
    | nil : Q2Forest α
    | cons : Q2Tree α → Q2Forest α → Q2Forest α
end
mutual
  inductive Q2Even : Nat → Prop where
    | zero : Q2Even 0
    | succ {n : Nat} : Q2Odd n → Q2Even (Nat.succ n)
  inductive Q2Odd : Nat → Prop where
    | succ {n : Nat} : Q2Even n → Q2Odd (Nat.succ n)
end

private inductive Q2Hidden where
  | unit
noncomputable def q2PrivateRoundtrip : Nat :=
  @Q2Hidden.rec (fun _ => Nat) 0 Q2Hidden.unit

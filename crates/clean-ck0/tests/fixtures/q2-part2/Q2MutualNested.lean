import Init.Prelude
universe u
mutual
  inductive Q2MutualTree (α : Type u) : Type u where
    | node : List (Q2MutualForest α) → Q2MutualTree α
  inductive Q2MutualForest (α : Type u) : Type u where
    | nil : Q2MutualForest α
    | cons : Q2MutualTree α → Q2MutualForest α → Q2MutualForest α
end
#print Q2MutualTree.rec
#print Q2MutualForest.rec

noncomputable def q2MutualNestedFold (t : Q2MutualTree PUnit) : Nat :=
  Q2MutualTree.rec
    (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => Nat.succ ih) 0 (fun _ _ a b => Nat.add a b) 0
    (fun _ _ a b => Nat.add a b) t

theorem q2MutualNestedIota : q2MutualNestedFold (.node [.cons (.node []) .nil]) = 2 := rfl

inductive Q2Vec (α : Type u) : Nat → Type u where
  | nil : Q2Vec α 0
  | cons {n : Nat} : α → Q2Vec α n → Q2Vec α (Nat.succ n)
inductive Q2IndexedTree (α : Type u) : Type u where
  | node (n : Nat) : Q2Vec (Q2IndexedTree α) n → Q2IndexedTree α
#print Q2IndexedTree.rec

noncomputable def q2IndexedNestedFold (t : Q2IndexedTree PUnit) : Nat :=
  Q2IndexedTree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (fun _ _ ih => Nat.succ ih) 0 (fun {_} _ _ a b => Nat.add a b) t

theorem q2IndexedNestedIota :
  q2IndexedNestedFold (.node 1 (.cons (.node 0 .nil) .nil)) = 2 := rfl

mutual
  inductive Q2ContainerA (α : Type u) : Type u where
    | leaf : α → Q2ContainerA α
  inductive Q2ContainerB (α : Type u) : Type u where
    | leaf : α → Q2ContainerB α
end
inductive Q2UsesContainerB (α : Type u) : Type u where
  | leaf : Q2UsesContainerB α
  | node : Q2ContainerB (Q2UsesContainerB α) → Q2UsesContainerB α
#print Q2UsesContainerB.rec

private inductive Q2PrivateRose where
  | node : List Q2PrivateRose → Q2PrivateRose
noncomputable def q2PrivateNestedFold (t : Q2PrivateRose) : Nat :=
  Q2PrivateRose.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ ih => Nat.succ ih) 0 (fun _ _ a b => Nat.add a b) t
theorem q2PrivateNestedIota : q2PrivateNestedFold (.node []) = 1 := rfl

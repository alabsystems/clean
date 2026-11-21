structure CallNode where
  kind : Bool
  results : Nat

def applyNode (k : Nat) (node : CallNode) (values : List Nat) : Option Nat :=
  if node.results = values.length then some k else none

def observe : Option Nat → Nat
  | none => 0
  | some v => v + 1

theorem inferredFoldedCall
    (H : Nat → Nat → List Nat → Nat → Prop)
    (sound : ∀ (k : Nat) (node : CallNode) (vs : List Nat) (r : Nat),
      H k node.results vs r → observe (applyNode k node vs) = r)
    (join : Nat → (Nat → Option Nat) → Nat) (seq : Nat → (Nat → Nat → Prop) → Nat → Prop)
    (lift : ∀ (x : Nat) (f : Nat → Option Nat) (P : Nat → Nat → Prop) (r : Nat),
      (∀ v r, P v r → observe (f v) = r) → seq x P r → join x f = r)
    (x k n r : Nat) (hs : seq x (fun v => H k n [v]) r) :
    join x (fun v => applyNode k ⟨false,n⟩ [v]) = r := by
  exact lift _ _ _ _ (fun v r hb => sound _ _ _ _ hb) hs

structure CallNode where
  kind : Bool
  results : Nat

def applyNode (k : Nat) (node : CallNode) (values : List Nat) : Option Nat :=
  if node.results = values.length then some k else none

def observe : Option Nat → Nat
  | none => 0
  | some v => v + 1

structure CallCell where
  value : Nat

inductive Sequenced {α : Type} (input : Option α) (post : α → Nat → Prop) : Nat → Prop where
  | ok (value : α) (r : Nat) : input = some value → post value r → Sequenced input post r
  | fail : input = none → Sequenced input post 0

inductive Bindings (k : Nat) (results : Nat) (values : List Nat) : Nat → Prop where
  | ready (r : Nat) : results = values.length → r = k → Bindings k results values r

inductive CellRead (ptr : Bool) (post : CallCell → Nat → Prop) : Nat → Prop where
  | ready (c : CallCell) (r : Nat) : post c r → CellRead ptr post r

theorem nestedTypedCallback
    (sound : ∀ (k : Nat) (node : CallNode) (vs : List Nat) (r : Nat),
      Bindings k node.results vs r → observe (applyNode k node vs) = r)
    (join : {α : Type} → Option α → (α → Option Nat) → Option Nat)
    (reject : Bool → Option Unit)
    (source : Nat → Option Bool) (check : Nat → Option Unit)
    (access : Bool → (CallCell → Option Nat) → Option Nat)
    (lift : ∀ {α : Type} (x : Option α) (f : α → Option Nat) (P : α → Nat → Prop) (r : Nat),
      (∀ v r, P v r → observe (f v) = r) → Sequenced x P r → observe (join x f) = r)
    (read : ∀ (ptr : Bool) (P : CallCell → Nat → Prop) (f : CallCell → Option Nat),
      (∀ c r, P c r → observe (f c) = r) → ∀ r, Sequenced (reject ptr) (fun _ => CellRead ptr P) r → observe (access ptr f) = r)
    (x k n r : Nat)
    (hs : Sequenced (source x) (fun ptr => Sequenced (reject ptr) (fun _ => CellRead ptr (fun c => Sequenced (check c.value)
       (fun _ => Bindings k n [c.value])))) r) :
    observe (join (source x) (fun p => access p (fun c => join (check c.value)
        (fun _ => applyNode k ⟨false, n⟩ [c.value])))) = r := by
  exact lift _ _ _ _ (fun ptr r hp => read ptr _ _
    (fun c r hc => lift _ _ _ _ (fun _ r hb => sound _ _ _ _ hb) hc) _ hp) hs

inductive Witness (p : α → Prop) : α → Prop where
  | intro {x} : p x → Witness p x
def witnessZero : Witness (fun n : Nat => n = 0) 0 := Witness.intro rfl

def Signature (A : Type u) := A → Prop
inductive ViaAlias (sig : Signature A) : A → Prop where
  | intro {x} : sig x → ViaAlias sig x
def aliasZero : ViaAlias (fun n : Nat => n = 0) 0 := ViaAlias.intro rfl

inductive Both (p : α → Prop) (q : β → Prop) : α → β → Prop where
  | intro {x y} : p x → q y → Both p q x y
def bothZero : Both (fun n : Nat => n = 0) (fun b : Bool => b = true) 0 true := Both.intro rfl rfl

inductive HeaderIndex (p : α → Prop) : Nat → Prop where
  | zero : HeaderIndex p 0
def headerZero : HeaderIndex (fun n : Nat => n = 0) 0 := HeaderIndex.zero

inductive Bounded (x : Fin n) : Prop where
  | intro : Bounded x

theorem witnessElim {α} {p : α → Prop} {x : α} (h : Witness p x) : p x := by
  cases h with
  | intro hp => exact hp

class OwnBox (p : Prop) (α : Type) (x : α) where
  val : α
section
variable (p : Prop)
axiom axiomOwn (x : α) (hp : p) : Nat
opaque opaqueOwn (x : α) (hp : p) : Nat
opaque opaqueBodyOwn (x : α) (hp : p) : α := x
partial def partialOwn (x : α) (hp : p) : Nat := partialOwn x hp
instance instanceOwn (x : α) : OwnBox p α x := ⟨x⟩
end
noncomputable def useAxiom : Nat := @axiomOwn True Nat 3 True.intro
def useOpaque : Nat := @opaqueOwn True Nat 3 True.intro
def useOpaqueBody : Nat := @opaqueBodyOwn True Nat 3 True.intro
def usePartial : Nat := @partialOwn True Nat 3 True.intro
def useInstance : Nat := (@instanceOwn True Nat 3).val
section
variable (p : Prop) [Decidable p]
axiom prunedAxiomOwn (x : Nat) (hp : p) : Nat
end
noncomputable def prunedAxiomPositional : Nat := @prunedAxiomOwn True 3 True.intro
noncomputable def prunedAxiomNamed : Nat := prunedAxiomOwn (p := True) (x := 3) (hp := True.intro)

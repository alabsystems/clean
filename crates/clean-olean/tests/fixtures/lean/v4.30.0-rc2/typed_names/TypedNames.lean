prelude

universe «u.dot»

def Alias.value : Type 1 := Type
def «Alias.value» : Type 1 := Type → Type
def «07» : Type 1 := Prop → Type

def readNested : Type 1 := Alias.value
def readQuoted : Type 1 := «Alias.value»
def read07 : Type 1 := «07»

noncomputable def keep : ∀ (α : Sort «u.dot»), α → α := fun _ a => a

theorem nestedExpected : ∀ (p : Prop), p → p := fun _ h => h
theorem quotedExpected : ∀ (p : Prop), p → p := fun _ h => h
theorem digitExpected : ∀ (p : Prop), p → p := fun _ h => h

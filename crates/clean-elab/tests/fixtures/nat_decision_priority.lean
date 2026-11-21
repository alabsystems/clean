def plainCarrierLe (a b : UInt32) : Bool := a ≤ b
def plainCarrierLt (a b : UInt32) : Bool := a < b
instance (priority := 800) lowLe (a b : Nat) : Decidable (a ≤ b) := Nat.decLe a b
instance (priority := 800) lowLt (a b : Nat) : Decidable (a < b) := Nat.decLt a b
def belowLe (a b : Nat) : Bool := a ≤ b
def belowLt (a b : Nat) : Bool := a < b
instance (priority := 1000) equalLe (a b : Nat) : Decidable (a ≤ b) := Nat.decLe a b
instance (priority := 1000) equalLt (a b : Nat) : Decidable (a < b) := Nat.decLt a b
def tiedLe (a b : Nat) : Bool := a ≤ b
def tiedLt (a b : Nat) : Bool := a < b
instance (priority := 1200) highLe (a b : Nat) : Decidable (a ≤ b) := Nat.decLe a b
def strictAfterHighLe (a b : Nat) : Bool := a < b
def carrierAfterHighLe (a b : UInt32) : Bool := a < b
instance (priority := 1200) highLt (a b : Nat) : Decidable (a < b) := Nat.decLt a b
def aboveLe (a b : Nat) : Bool := a ≤ b
def aboveLt (a b : Nat) : Bool := a < b
abbrev DecisionNumber := Nat
def aliasLt (a b : DecisionNumber) : Bool := a < b
def otherCarrierLe (a b : UInt32) : Bool := a ≤ b
def otherCarrierLt (a b : UInt32) : Bool := a < b

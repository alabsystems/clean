class Tag (α : Type) where
  tag : α → Nat

instance : Tag Nat := ⟨fun x => x⟩
@[default_instance] instance : Tag Int := ⟨fun x => x.toNat + 100⟩

-- A user default instance answers only once nothing else pins the goal: the
-- argument's `Nat` comes first.
def dRedex : Nat := (fun k => Tag.tag k) (5 : Nat)
theorem dRedex_eq : dRedex = 5 := rfl

class TagA (α : Type) where
  tag : α → Nat

instance : TagA Nat := ⟨fun x => x⟩
instance instTagAInt : TagA Int := ⟨fun x => x.toNat + 100⟩
attribute [default_instance] instTagAInt

def aRedex : Nat := (fun k => TagA.tag k) (5 : Nat)
theorem aRedex_eq : aRedex = 5 := rfl

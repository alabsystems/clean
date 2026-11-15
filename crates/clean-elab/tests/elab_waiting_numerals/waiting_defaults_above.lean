-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
-- One above `instOfNatNat`'s priority 100 the user default applies first.
-- (`let k := id 5; Tag.tag (k - 7)`, 100 in Lean, is still refused: Clean
-- does not carry the default through `k - 7`'s operator goal.)
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
@[default_instance 101] instance : Tag Int := ⟨fun x => x.toNat + 100⟩
def tSub : Nat := let k := 5; Tag.tag k + Tag.tag (k - 7)

theorem tSub_eq : tSub = 205 := rfl

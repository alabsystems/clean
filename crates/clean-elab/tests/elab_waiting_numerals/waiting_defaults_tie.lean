-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
-- A user default at `instOfNatNat`'s own priority 100: the older pending goal
-- (the numeral's `OfNat ?α 5`) is defaulted first, so the numerals are `Nat`.
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
@[default_instance 100] instance : Tag Int := ⟨fun x => x.toNat + 100⟩
def tSub : Nat := let k := 5; Tag.tag k + Tag.tag (k - 7)
def tIdSub : Nat := let k := id 5; Tag.tag (k - 7)
def tFn : Nat := let f := fun k => Tag.tag (k - 7); f 5
def tMut : Nat := Id.run do
  let mut k := 5
  k := k - 7
  return Tag.tag k
def tBind : Nat := Id.run do
  let k ← pure 5
  return Tag.tag (k - 7)

theorem tSub_eq : tSub = 5 := rfl
theorem tIdSub_eq : tIdSub = 0 := rfl
theorem tFn_eq : tFn = 0 := rfl
theorem tMut_eq : tMut = 0 := rfl
theorem tBind_eq : tBind = 0 := rfl

-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
-- At `instOfNatNat`'s own priority 100 the user's (newer) `OfNat` default is
-- tried first, so open numerals are still `W`.
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
instance : Tag Int := ⟨fun x => x.toNat + 100⟩
structure W where v : Nat
instance : Tag W := ⟨fun w => w.v + 1000⟩
@[default_instance 100] instance instW {n : Nat} : OfNat W n := ⟨⟨n⟩⟩
def wBare : Nat := Tag.tag 5
def wLet : Nat := let k := 5; Tag.tag k
def wId : Nat := let k := id 5; Tag.tag k
def wPair : Nat := let p := (5, 6); Tag.tag p.1
def wSome : Nat := let o := some 5; Tag.tag (o.getD 0)
def wFun : Nat := let f := fun x => x; Tag.tag (f 5)
def wHole : Nat := let k : _ := 5; Tag.tag k
def wAscr : Nat := let k := (5 : _); Tag.tag k
def wBodyLit : Nat := let k := id 5; Tag.tag k + Tag.tag 3
def wRedex : Nat := (fun k => Tag.tag k) (id 5)
def wDo : Nat := Id.run do
  let k := id 5
  return Tag.tag k
def wBind : Nat := Id.run do
  let k ← pure 5
  return Tag.tag k
def wMut : Nat := Id.run do
  let mut k := id 5
  k := k
  return Tag.tag k
def wNatPin : Nat := let k := id 5; Tag.tag (k : Nat)
def wIntPin : Nat := let k := 5; Tag.tag ((k : Int) - 7)
def wTop := 5
def wTopTag : Nat := Tag.tag wTop

theorem wBare_eq : wBare = 1005 := rfl
theorem wLet_eq : wLet = 1005 := rfl
theorem wId_eq : wId = 1005 := rfl
theorem wPair_eq : wPair = 1005 := rfl
theorem wSome_eq : wSome = 1005 := rfl
theorem wFun_eq : wFun = 1005 := rfl
theorem wHole_eq : wHole = 1005 := rfl
theorem wAscr_eq : wAscr = 1005 := rfl
theorem wBodyLit_eq : wBodyLit = 2008 := rfl
theorem wRedex_eq : wRedex = 1005 := rfl
theorem wDo_eq : wDo = 1005 := rfl
theorem wBind_eq : wBind = 1005 := rfl
theorem wMut_eq : wMut = 1005 := rfl
theorem wNatPin_eq : wNatPin = 5 := rfl
theorem wIntPin_eq : wIntPin = 100 := rfl
theorem wTopTag_eq : wTopTag = 1005 := rfl

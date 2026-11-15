-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
instance : Tag Int := ⟨fun x => x.toNat + 100⟩
def wId : Nat := let k := id 5; Tag.tag (k : Int) + Tag.tag k
def wMax : Nat := let k := max 5 3; Tag.tag k + Tag.tag (k : Int)
def wPair : Nat := let p := (5, 0); Tag.tag (p.1 : Int) + Tag.tag p.1
def wSome : Nat := let o := some 5; Tag.tag (o.getD 0 : Int) + Tag.tag (o.getD 0)
def wHole : Nat := let k : _ := 5; Tag.tag (k : Int) + Tag.tag k
def wAscrHole : Nat := let k := (5 : _); Tag.tag (k : Int) + Tag.tag k
def wHaveHole : Nat := have k : _ := 5; Tag.tag (k : Int) + Tag.tag k
def wChain : Nat := let k := 5; let j := k + 1; Tag.tag (j : Int) + Tag.tag k
def wPat : Nat := let (k, j) := (5, 0); Tag.tag (k : Int) + Tag.tag k + j
def wIf : Nat := let k := if true then 5 else 6; Tag.tag (k : Int) + Tag.tag k
def wFn : Nat := let f := fun x => x + 5; Tag.tag (f 0 : Int) + Tag.tag (f 0)
def wBodySub : Nat := let k := 5; Tag.tag (k - 7) + Tag.tag (k : Int)
def wDecide : Nat := let k := 5; (if k = 5 then Tag.tag k else 0) + Tag.tag (k : Int)
def wMut : Nat := Id.run do
  let mut k := 5
  k := k + 1
  return Tag.tag (k : Int) + Tag.tag k
def wFor : Nat := Id.run do
  let mut k := 0
  for i in [1, 2] do
    k := k + i
  return Tag.tag (k : Int) + Tag.tag k
def wBind : Nat := Id.run do
  let k ← pure 5
  return Tag.tag k + Tag.tag (k : Int)
def wRedexSub : Nat := (fun k => Tag.tag (k - 7) + Tag.tag (k : Int)) 5
def wRedexHead : Nat := (fun f => Tag.tag (f 0 : Int) + Tag.tag (f 0)) (fun x => x + 5)
def wLetRec : Nat :=
  let k := id 5
  let rec go : Nat → Nat
    | 0 => 0
    | n + 1 => go n
  go 2 + Tag.tag (k : Int) + Tag.tag k
def wNeg : Nat := let k := -5; Tag.tag k
def wNatOnly : Nat := let k := id 5; Tag.tag k
def wNested : Nat := let k := (let j := 5; j + 0); Tag.tag (k : Int) + Tag.tag k

theorem wId_eq : wId = 210 := rfl
theorem wMax_eq : wMax = 210 := rfl
theorem wPair_eq : wPair = 210 := rfl
theorem wSome_eq : wSome = 210 := rfl
theorem wHole_eq : wHole = 210 := rfl
theorem wAscrHole_eq : wAscrHole = 210 := rfl
theorem wHaveHole_eq : wHaveHole = 210 := rfl
theorem wChain_eq : wChain = 211 := rfl
theorem wPat_eq : wPat = 210 := rfl
theorem wIf_eq : wIf = 210 := rfl
theorem wFn_eq : wFn = 210 := rfl
theorem wBodySub_eq : wBodySub = 205 := rfl
theorem wDecide_eq : wDecide = 210 := rfl
theorem wMut_eq : wMut = 212 := rfl
theorem wFor_eq : wFor = 206 := rfl
theorem wBind_eq : wBind = 210 := rfl
theorem wRedexSub_eq : wRedexSub = 205 := rfl
theorem wRedexHead_eq : wRedexHead = 210 := rfl
theorem wLetRec_eq : wLetRec = 110 := rfl
theorem wNeg_eq : wNeg = 100 := rfl
theorem wNatOnly_eq : wNatOnly = 5 := rfl
theorem wNested_eq : wNested = 210 := rfl

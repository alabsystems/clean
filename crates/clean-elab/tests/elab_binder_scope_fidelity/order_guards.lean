class Tag (α : Type) where
  tag : α → Nat

instance : Tag Nat := ⟨fun x => x⟩
instance : Tag Int := ⟨fun x => x.toNat + 100⟩

-- A `let rec` header settles a pending numeral by defaulting, so `k : Nat`
-- even though the body later ascribes `k : Int`.
def lrCapture : Nat :=
  let k := 5
  let rec go : Nat → Nat
    | 0 => Tag.tag k
    | n + 1 => go n
  go 2 + Tag.tag (k : Int)
theorem lrCapture_eq : lrCapture = 110 := rfl

def lrHave : Nat :=
  have k := 5
  let rec go : Nat → Nat
    | 0 => Tag.tag k
    | n + 1 => go n
  go 2 + Tag.tag (k : Int)
theorem lrHave_eq : lrHave = 110 := rfl

def lrNoUse : Nat :=
  let k := 5
  let rec go : Nat → Nat
    | 0 => 0
    | n + 1 => go n
  go 2 + Tag.tag (k : Int) + Tag.tag k
theorem lrNoUse_eq : lrNoUse = 110 := rfl

def lrSum : Nat :=
  let k := 5 + 0
  let rec go : Nat → Nat
    | 0 => Tag.tag k
    | n + 1 => go n
  go 2 + Tag.tag (k : Int)
theorem lrSum_eq : lrSum = 110 := rfl

-- A type the body pins before the header is no longer pending there.
def lrAfterPin : Nat := let k := 5; Tag.tag (k : Int) + (let rec go : Nat → Nat
    | 0 => 0
    | n + 1 => go n
  go 1) + Tag.tag k
theorem lrAfterPin_eq : lrAfterPin = 210 := rfl

-- A β-redex binder is not a pending numeral: Lean's order stands.
def lrRedex : Nat := (fun k => let rec go : Nat → Nat
    | 0 => Tag.tag (k : Int)
    | n + 1 => go n
  go 2 + Tag.tag k) 5
theorem lrRedex_eq : lrRedex = 210 := rfl

-- A numeral `let` inside a β-redex is still settled by the header.
def lrRedexNumLet : Nat := (fun j => let k := 5; (let rec go : Nat → Nat
    | 0 => 0
    | n + 1 => go n
  go 1) + Tag.tag k + Tag.tag (k : Int) + j) 0
theorem lrRedexNumLet_eq : lrRedexNumLet = 110 := rfl

-- A numeral made with operators waits for the body like a bare one.
def numDiv : Nat := let k := 7 / 2; Tag.tag (k : Int) + Tag.tag k
theorem numDiv_eq : numDiv = 206 := rfl

def numSub : Nat := let k := 3 - 5; Tag.tag (k : Int) + Tag.tag k
theorem numSub_eq : numSub = 200 := rfl

-- So does a `let mut` numeral.
def mutLet : Nat := Id.run do
  let mut k := 5
  return Tag.tag (k : Int) + Tag.tag k
theorem mutLet_eq : mutLet = 210 := rfl

-- A multi-parameter goal that names `Int` still may not have its open input
-- pinned by the latest instance.
class Tg (α β : Type) where
  tg : β → Nat
instance : Tg Int Nat := ⟨fun x => x⟩
instance : Tg Int Int := ⟨fun x => x.toNat + 100⟩

def tgLet : Nat := let f := fun k => Tg.tg (α := Int) k; f 5
theorem tgLet_eq : tgLet = 5 := rfl

def tgRedex : Nat := (fun k => Tg.tg (α := Int) k) 5
theorem tgRedex_eq : tgRedex = 5 := rfl

class C2 (α β : Type) where
  v : α → β → Nat
instance : C2 Int Nat := ⟨fun a b => a.toNat + b + 100⟩
instance : C2 Nat Nat := ⟨fun a b => a + b⟩

def c2Redex : Nat := (fun k => C2.v k (0 : Nat) + Tag.tag (k : Int)) 5
theorem c2Redex_eq : c2Redex = 210 := rfl

def c2Let : Nat := let f := fun k => C2.v k (0 : Nat) + Tag.tag (k : Int); f 5
theorem c2Let_eq : c2Let = 210 := rfl

class Tg2 (α β : Type) where
  tg : β → Nat
instance : Tg2 Nat Int := ⟨fun x => x.toNat + 100⟩
instance : Tg2 Nat Nat := ⟨fun x => x⟩

def tg2Redex : Nat := (fun k => Tg2.tg (α := Nat) k + Tag.tag (k : Int)) 5
theorem tg2Redex_eq : tg2Redex = 210 := rfl

-- `<|>` unifies its operands' types (`binop_lazy%`) before the instance is
-- synthesized, so `none`'s `Option ?α` meets `Option Nat` there.
def orElseNone : Option Nat := none <|> some 3
theorem orElseNone_eq : orElseNone = some 3 := rfl

-- An out-parameter is the search's to fill.
class Cv (α : Type) (β : outParam Type) where
  cv : α → β
instance : Cv Nat Int := ⟨fun n => (n : Int) - 10⟩

def cvOut : Nat := Tag.tag (Cv.cv (5 : Nat))
theorem cvOut_eq : cvOut = 100 := rfl

-- The expected type reaches the redex's result.
def negRedex : Int := (fun k => -k + 0) 5
theorem negRedex_eq : negRedex = -5 := rfl

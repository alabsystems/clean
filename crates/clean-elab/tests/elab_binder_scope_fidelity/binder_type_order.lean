class Tag (α : Type) where
  tag : α → Nat

instance : Tag Nat := ⟨fun x => x⟩
instance : Tag Int := ⟨fun x => x.toNat + 100⟩

-- The binder's type comes from the body (`k : Int`), not from the argument.
def m2 : Nat := (fun k => Tag.tag (k : Int) + Tag.tag k) 5
theorem m2_eq : m2 = 210 := rfl

-- A `Nat` argument is coerced to the binder's `Int`.
def mNat (n : Nat) : Nat := (fun k => Tag.tag (k : Int) + Tag.tag k) n
theorem mNat_five : mNat 5 = 210 := rfl

-- Only the first binder is pinned; the second defaults to `Nat`.
def mTwo : Nat := (fun a b => Tag.tag (a : Int) + Tag.tag a + Tag.tag b) 5 5
theorem mTwo_eq : mTwo = 215 := rfl

-- A body that matches on the binder.
def mMatch : Nat := (fun p => match p with | x => Tag.tag (x : Int) + Tag.tag p) 5
theorem mMatch_eq : mMatch = 210 := rfl

-- An `if` condition pins the binder.
def mIf : Nat := (fun k => if (k : Int) < 0 then 0 else Tag.tag k) 5
theorem mIf_eq : mIf = 105 := rfl

-- `Tag ?α` waits for the argument instead of taking the latest instance.
def mOpen : Nat := let f := fun k j => Tag.tag (j : Int) + Tag.tag k; f 5 7
theorem mOpen_eq : mOpen = 112 := rfl

-- An unannotated numeral `let`/`have`/do-`let` takes its type from the body.
def mLet : Nat := let k := 5; Tag.tag (k : Int) + Tag.tag k
theorem mLet_eq : mLet = 210 := rfl

def mHave : Nat := have k := 5; Tag.tag (k : Int) + Tag.tag k
theorem mHave_eq : mHave = 210 := rfl

def mDo : Nat := Id.run do
  let k := 5
  return Tag.tag (k : Int) + Tag.tag k
theorem mDo_eq : mDo = 210 := rfl

-- Nothing pins it: still `Nat`.
def mLetNat := let k := 5; k - 7
theorem mLetNat_eq : mLetNat = 0 := rfl

-- A binder used as a function head still elaborates (the let-chain fallback).
def mHead : Nat := (fun f x => f x) (fun n => n + 1) 10
theorem mHead_eq : mHead = 11 := rfl

-- An open `Tag ?α` is pinned by the argument, not by the latest instance.
def twice {α : Type} [Tag α] (x : α) : Nat := Tag.tag x + Tag.tag x
def mTwice : Nat := twice 5
theorem mTwice_eq : mTwice = 10 := rfl

-- `@[default_instance]` on an instance answers an open goal; a later plain
-- instance does not.
class Df (α : Type) where
  v : Nat
instance dfNat : Df Nat where v := 3
@[default_instance] instance dfBool : Df Bool where v := 4
instance dfNat2 : Df Nat where v := 5
def dfGet {α : Type} [Df α] : Nat := Df.v (α := α)
def dfOpen : Nat := dfGet
theorem dfOpen_eq : dfOpen = 4 := rfl

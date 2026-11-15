inductive EmptyList : List Nat → Prop where
  | intro {xs} : xs.length = 0 → EmptyList xs
def emptyProof : EmptyList [] := EmptyList.intro rfl

inductive SameLen : List Nat → List Nat → Prop where
  | intro {xs ys} : xs.length = ys.length → SameLen xs ys
def sameProof : SameLen [] [] := SameLen.intro rfl

inductive Scoped : List Nat → Prop where
  | intro {xs} : xs.length = 0 → ((xs : Nat) → xs = xs) → Scoped xs
def scopedProof : Scoped [] := Scoped.intro rfl (fun _ => rfl)

structure Row where
  value : Nat
inductive ZeroRow : Row → Prop where
  | intro {row} : row.value = 0 → ZeroRow row
def rowProof : ZeroRow (Row.mk 0) := ZeroRow.intro rfl

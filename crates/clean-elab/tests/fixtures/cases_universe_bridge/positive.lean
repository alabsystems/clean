def pick {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: xs, i + 1 => pick xs i

theorem autoCases (xs : List α) (i : Nat) : True := by
  cases hx : pick xs i with
  | none => trivial
  | some a => trivial

theorem explicitCases {α : Type u} (xs : List α) (i : Nat) : True := by
  cases hx : pick xs i with
  | none => trivial
  | some a => trivial

def choose (d : α) (xs : List α) (i : Nat) : α := by
  cases hx : pick xs i with
  | none => exact d
  | some a => exact a

theorem typesCases (xs : List (Type u)) (i : Nat) : True := by
  cases hx : pick xs i with
  | none => trivial
  | some a => trivial

theorem nestedCases (xs : List α) (i : Nat) : True := by
  induction xs generalizing i with
  | nil => trivial
  | cons d xs ih =>
    cases i with
    | zero => trivial
    | succ i =>
      cases hx : pick xs i with
      | none => trivial
      | some a => trivial

theorem matchedCases (xs : List α) (i : Nat) : True := by
  match hx : pick xs i with
  | none => trivial
  | some a => trivial

def inferredHave (xs : List α) (i : Nat) : Option α := by
  have result := pick xs i
  exact result

theorem inductionTarget (xs : List α) (i : Nat) : True := by
  induction pick xs i with
  | none => trivial
  | some a => trivial

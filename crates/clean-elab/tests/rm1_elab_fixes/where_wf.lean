-- RM1 fixture (K5 probe b2): well-founded recursion in a `where` helper.
def countUp (limit : Nat) : Nat :=
  go 0
where
  go (i : Nat) : Nat :=
    if h : i < limit then go (i + 1) else i
  termination_by limit - i

def sumTo (n : Nat) : Nat :=
  loop 0 0
where
  loop (i acc : Nat) : Nat :=
    if i < n then loop (i + 1) (acc + i) else acc
  termination_by n - i

-- A parameter every call passes unchanged, in the last position: the
-- structural fallback would pick it, so the well-founded route must not
-- apply the structural pass-through gate.
def passLast (limit : Nat) (k : Nat) : Nat :=
  go 0 k
where
  go (i k : Nat) : Nat :=
    if i < limit then go (i + 1) k else i + k
  termination_by limit - i

-- A hinted helper followed by another helper: each hint ends where the next
-- helper's header starts.
def twoHelpers (limit : Nat) : Nat :=
  up 0 + down limit + other limit
where
  up (i : Nat) : Nat :=
    if i < limit then up (i + 1) else i
  termination_by limit - i
  down (i : Nat) : Nat :=
    if h : i < limit then down (i + 1) else i
  termination_by limit - i
  decreasing_by simp_wf; omega
  other (n : Nat) : Nat := n

-- The same helper inside a namespace (TrustIr's shape), read from outside.
namespace B2
def countUp (limit : Nat) : Nat :=
  go 0
where
  go (i : Nat) : Nat :=
    if h : i < limit then go (i + 1) else i
  termination_by limit - i
end B2

theorem countUp_three : countUp 3 = 3 := by decide
theorem sumTo_four : sumTo 4 = 6 := by decide
theorem passLast_three : passLast 3 10 = 13 := by decide
theorem twoHelpers_three : twoHelpers 3 = 9 := by decide
theorem b2_countUp_three : B2.countUp 3 = 3 := by decide

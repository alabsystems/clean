inductive Packed where
  | mk {flag : Bool} ⦃tag : Nat⦄ [inst : Inhabited Nat] (value : Nat) (h : value = 0) : Packed

theorem case_normal (p : Packed) : ∃ n : Nat, n = 0 := by
  cases p with
  | mk n h => exact ⟨n, h⟩

theorem case_explicit (p : Packed) : ∃ n : Nat, n = 0 := by
  cases p with
  | @mk flag tag inst n h => exact ⟨n, h⟩

theorem induction_normal (p : Packed) : ∃ n : Nat, n = 0 := by
  induction p with
  | mk n h => exact ⟨n, h⟩

theorem induction_explicit (p : Packed) : ∃ n : Nat, n = 0 := by
  induction p with
  | @mk flag tag inst n h => exact ⟨n, h⟩

inductive Tree where
  | leaf {flag : Bool} (value : Nat) : Tree
  | branch {flag : Bool} (a b : Tree) : Tree

theorem recursive_normal (t : Tree) : True := by
  induction t with
  | leaf n => have x : Nat := n; trivial
  | branch a b ih => exact ih

theorem recursive_explicit (t : Tree) : True := by
  induction t with
  | @leaf flag n => have x : Nat := n; trivial
  | @branch flag a b ih₁ ih₂ => exact ih₂

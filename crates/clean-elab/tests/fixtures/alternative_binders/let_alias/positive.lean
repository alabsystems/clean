inductive Packed where
  | mk {flag : Bool} ⦃tag : Nat⦄ [inst : Inhabited Nat] (value : Nat) (h : value = 0) : Packed

theorem let_alias_cases_ordinary (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 0 := by
  let alias : Packed := p
  cases p with
  | mk n h => exact ⟨alias, rfl, n, h⟩

theorem let_alias_cases_explicit (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 0 := by
  let alias : Packed := p
  cases p with
  | @mk flag tag inst n h => exact ⟨alias, rfl, n, h⟩

theorem let_alias_induction_ordinary (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 0 := by
  let alias : Packed := p
  induction p with
  | mk n h => exact ⟨alias, rfl, n, h⟩

theorem let_alias_induction_explicit (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 0 := by
  let alias : Packed := p
  induction p with
  | @mk flag tag inst n h => exact ⟨alias, rfl, n, h⟩

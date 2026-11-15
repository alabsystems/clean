inductive Packed where
  | mk {flag : Bool} ⦃tag : Nat⦄ [inst : Inhabited Nat] (value : Nat) (h : value = 0) : Packed

theorem let_alias_cases_ordinary_wrong_equation (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 1 := by
  let alias : Packed := p
  cases p with
  | mk n h => exact ⟨alias, rfl, n, h⟩

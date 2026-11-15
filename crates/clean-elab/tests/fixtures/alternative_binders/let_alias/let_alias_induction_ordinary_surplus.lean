inductive Packed where
  | mk {flag : Bool} ⦃tag : Nat⦄ [inst : Inhabited Nat] (value : Nat) (h : value = 0) : Packed

theorem let_alias_induction_ordinary_surplus (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 0 := by
  let alias : Packed := p
  induction p with
  | mk n h extra => exact ⟨alias, rfl, n, h⟩

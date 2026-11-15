inductive Packed where
  | mk {flag : Bool} ⦃tag : Nat⦄ [inst : Inhabited Nat] (value : Nat) (h : value = 0) : Packed

theorem let_alias_induction_explicit_wrong_equation (p : Packed) : ∃ q : Packed, q = p ∧ ∃ n : Nat, n = 1 := by
  let alias : Packed := p
  induction p with
  | @mk flag tag inst n h => exact ⟨alias, rfl, n, h⟩

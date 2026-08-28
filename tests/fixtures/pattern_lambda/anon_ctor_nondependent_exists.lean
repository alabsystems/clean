-- Control for `anon_ctor_dependent_exists.lean`: anonymous-constructor
-- patterns whose lowering never opens a nested `Exists.intro` field against
-- an earlier sibling —
--
--   * a TWO-leaf pattern over `∃ x, q x` (the top-level arm path, which
--     already opened its dependent field types with `open_field_type_with_fvars`),
--   * a THREE-leaf pattern whose inner constructor is `And.intro` (fields
--     independent of each other),
--   * a two-leaf pattern over `p ∧ q` and over a non-dependent `∃ _ : p, q`.
--
-- These passed BEFORE the dependent-nested repair and must keep passing: they
-- pin that the repair touched only the nested dependent shape.

universe u

theorem exists_mem_of_exists {α : Sort u} {p q : α → Prop}
    (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩

theorem exists_of_exists_and {α : Sort u} {p q : α → Prop} :
    (∃ x, p x ∧ q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩

theorem and_swap_pattern {p q : Prop} : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ ↦ ⟨hq, hp⟩

theorem exists_const_witness {p q : Prop} : (∃ _ : p, q) → p ∧ q :=
  fun ⟨hp, hq⟩ ↦ ⟨hp, hq⟩

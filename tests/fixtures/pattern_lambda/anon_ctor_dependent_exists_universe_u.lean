-- The `universe u` sibling of `anon_ctor_dependent_exists.lean`.
--
-- That fixture's header recorded, and deliberately did not fix, a neighbouring
-- refusal Lane BVAR hit while repairing the nested-constructor loose bvar:
-- rewriting `Sort*` to a DECLARED `universe u` / `{α : Sort u}` made the same
-- six declarations fail with
--
--     cannot assign rigid universe parameter u := 1
--
-- so the fixture was pinned to `Sort*` to keep the two causes apart. This file
-- is the other half, held to the same Mathlib text with only the section
-- variable line rewritten, so the pair now covers both spellings.
--
-- The cause was not the section variable and not the rigidity — `u` IS a
-- declared parameter and must not be assignable. It was `elab_hole` minting the
-- `_` holes in `H _ hp` / `H _ _ h'` with a hardcoded `Sort 1` type, which
-- forced `u := 1` and hit the (correct) refusal. See
-- `tests/fixtures/universes/p37_hole_universe_polymorphic.lean`; the refusal
-- itself is pinned intact by p39.
--
-- `And.exists` is omitted: its `{p q : Prop}` binders never mention `α`, so it
-- is identical to the `Sort*` file's copy and would only duplicate coverage.

universe u

section BoundedQuantifiers

variable {α : Sort u} {r p q : α → Prop} {P Q : ∀ x, p x → Prop}

theorem bex_def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩⟩

theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂

theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩

theorem BEx.imp_right (H : ∀ x h, P x h → Q x h) : (∃ x h, P x h) → ∃ x h, Q x h
  | ⟨_, _, h'⟩ => ⟨_, _, H _ _ h'⟩

theorem BEx.imp_left (H : ∀ x, p x → q x) : (∃ (x : _) (_ : p x), r x) → ∃ (x : _) (_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩

theorem exists_of_exists_mem : (∃ (x : _) (_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩

end BoundedQuantifiers

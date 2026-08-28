-- Anonymous-constructor patterns over a DEPENDENT `∃` — the shape where a
-- later component's type mentions an earlier one and the pattern has THREE
-- leaves, so the inner `Exists.intro` is lowered as a NESTED constructor
-- pattern.
--
-- Measured 2026-08-21 on `Mathlib/Logic/Basic.lean` through `clean check`
-- (docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md): five of
-- these declarations failed with the kernel's verbatim
--
--     Unbound variable index: 0
--
-- Re-measured 2026-08-22 against the repair reverted (release profile): SIX
-- of the seven are rejected pre-repair. `BEx.elim` — whose arm is
-- multi-discriminant, `| ⟨a, h₁, h₂⟩, h' => …` — fails instead with
-- `TypeMismatch … "cannot unify expressions of different shape:
-- Discriminant(0) vs Discriminant(1)"`, the same loose sibling `BVar` landing
-- in the arm's expected type rather than in the term handed to the kernel.
-- `BEx.intro` is the in-family control: an anonymous-constructor CONSTRUCTION
-- over the same dependent `∃`, green before the repair and after it.
--
-- The declarations are Mathlib's own text (lines 597 and 752–780) — every
-- block byte-identical, including the `Sort*` section variable line of
-- `section BoundedQuantifiers`. They are
-- deliberately NOT rewritten to `universe u` / `Sort u`: with a declared
-- universe parameter, the `_` holes in `H _ hp` / `H _ _ h'` trip a separate,
-- pre-existing level-solver refusal (`cannot assign rigid universe parameter
-- u := 1`, the U2 class — measured 2026-08-21, not this fixture's subject).
--
-- UPDATE 2026-08-22: that U2 refusal is FIXED (`elab_hole` was minting the
-- hole's type with a hardcoded `Sort 1`; see
-- `tests/fixtures/universes/p37_hole_universe_polymorphic.lean`). This file
-- stays on `Sort*` so it keeps testing exactly what it tested before; the
-- declared-parameter spelling now has its own green sibling,
-- `anon_ctor_dependent_exists_universe_u.lean`.

theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ ↦ ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ ↦ ⟨⟨hp, hq⟩, H⟩⟩

section BoundedQuantifiers

variable {α : Sort*} {r p q : α → Prop} {P Q : ∀ x, p x → Prop}

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

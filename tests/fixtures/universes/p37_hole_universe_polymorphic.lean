-- U2 / rung 4 sibling — A `_` HOLE MUST NOT PIN ITS OWN UNIVERSE.
--
-- `elab_hole` used to mint the hole's type metavariable as
-- `fresh_meta(Expr::type_())`, i.e. `?t : Sort 1`: an assertion, licensed by
-- nothing the user wrote, that whatever the hole turns out to be lives in
-- `Type 0`. `unify_meta`'s Sort arm enforces that on assignment, so the sort of
-- the value the hole resolves to was unified against the literal `1`. Measured
-- 2026-08-22 against the release binary, one line per row, all the SAME body
-- `H _ hp` differing only in `α`'s sort:
--
--   α : Prop    (Sort 0)  PASS  -- only via cumulativity 0 ≤ 1
--   α : Type    (Sort 1)  PASS  -- only because it matched the literal
--   α : Type 1  (Sort 2)  FAIL  -- "universe level conflict: Succ(Zero) vs Succ(Succ(..))"
--   α : Sort u  (rigid)   FAIL  -- "cannot assign rigid universe parameter u := 1"
--   α : Sort*   (fresh)   PASS  -- and SILENTLY MONOMORPHIZED to Type 0
--
-- The `Sort*` row is why this fixture does not stop at "it elaborates". A
-- non-rigid `Sort*` param accepts `?u_n := 1`, so the declaration was accepted
-- while registering a strictly weaker theorem than the one written, and only a
-- downstream use at `Prop` or `Type 1` discovered it — at a distance, as an
-- unrelated-looking kernel mismatch. `usedAtProp` / `usedAtType1` below are
-- that discriminator: they instantiate `polySortStar` at `Sort 0` and `Sort 2`,
-- which a `Type 0`-collapsed version cannot satisfy. Delete them and this
-- fixture would pass on the bug.
--
-- The fix is Lean's `mkFreshTypeMVar`: the hole's type is `Sort ?u` with a
-- FRESH LEVEL METAVARIABLE, solved from context. Rigid refusal is untouched —
-- see p39, where the hole's universe is genuinely forced and `u := 1` is still
-- refused with this same message.

-- The rigid row: `u` is a declared parameter and must survive as one.
universe u
theorem polyRigid {α : Sort u} {p q : α → Prop} (H : ∀ x, p x → q x) (x : α)
    (hp : p x) : q x := H _ hp

-- The high-universe row.
theorem polyType1 {α : Type 1} {p q : α → Prop} (H : ∀ x, p x → q x) (x : α)
    (hp : p x) : q x := H _ hp

-- The silent-monomorphization row.
theorem polySortStar {α : Sort*} {p q : α → Prop} (H : ∀ x, p x → q x) (x : α)
    (hp : p x) : q x := H _ hp

theorem polyTypeStar {α : Type*} {p q : α → Prop} (H : ∀ x, p x → q x) (x : α)
    (hp : p x) : q x := H _ hp

-- The two rows that passed for the wrong reason, kept as controls.
theorem polyProp {α : Prop} {p q : α → Prop} (H : ∀ x, p x → q x) (x : α)
    (hp : p x) : q x := H _ hp

theorem polyType {α : Type} {p q : α → Prop} (H : ∀ x, p x → q x) (x : α)
    (hp : p x) : q x := H _ hp

-- THE DISCRIMINATORS: `polySortStar` is only genuinely universe-polymorphic if
-- it instantiates BELOW and ABOVE `Type 0`. Both were rejected before the fix.
theorem usedAtProp {p q : True → Prop} (H : ∀ x, p x → q x) (x : True)
    (hp : p x) : q x := polySortStar H x hp

theorem usedAtType1 {β : Type 1} {p q : β → Prop} (H : ∀ x, p x → q x) (x : β)
    (hp : p x) : q x := polySortStar H x hp

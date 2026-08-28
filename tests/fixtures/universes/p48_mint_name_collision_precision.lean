-- P48 — the PRECISION companion to p47 (U2 stage-3 deferral 1, 2026-08-26).
--
-- p47 pins that a user-written universe name is refused LOUDLY when its
-- declaration monomorphizes it — including the `u_0` spelling that used to
-- collide with a mint and be solved away in silence. That MUST_FAIL probe
-- cannot, on its own, tell a precise refusal from an over-broad one: an
-- elaborator that simply rejected every `u_N`-spelled universe, or that made
-- every level hole rigid, would satisfy p47 exactly as well as the real fix.
--
-- SEVEN declarations. Five are neighbouring SHAPES — four ways a `u_N`
-- spelling legitimately reaches a declaration, plus p49's rename control —
-- and two are CONTROLS added 2026-08-26b: an arity witness (1b) and p51's
-- guillemet control (4b). All PASS today and must keep passing. The refusals
-- p47 and p51 pin each narrow a decision; neither may widen a refusal at all.
--
-- Same discipline as p46 relative to p21.
--
-- AMENDED 2026-08-26b (mint-namespace reservation). Shape 1's header used to
-- read "Clean conflates the hole and the written name into ONE parameter
-- here, where Lean would keep two; that over-constraint is … the `LevelMVarId`
-- refactor's business." That is no longer true and the correction is the point
-- of `useIdCollide` below: universe metavariables are now minted into a
-- reserved space no surface identifier can reach (`?u_0`, `?u_1`, … —
-- `crate::level_mint::MINT_PREFIX`), so the hole and the written `u_0` are
-- DIFFERENT levels and `idCollide` carries two universe parameters. p49, which
-- pinned the cost of the conflation, is a positive fixture as of the same day.

-- 1. THE COLLISION ITSELF, used legitimately — except that there is no
--    collision left to have. `Sort _` mints `?u_0`; the written `u_0` is a
--    different name and therefore a different level. The declaration is
--    polymorphic in both.
def idCollide (β : Sort _) (x : β) (γ : Sort u_0) (y : γ) : γ := y

-- 1b. THE ARITY WITNESS for shape 1, and it is not optional: `idCollide`
--     elaborating proves nothing about how many universes survived — it
--     elaborated when the two were conflated, too. This instantiates it at two
--     DIFFERENT levels (`γ : Sort 1`, i.e. `Nat`; `β : Sort 0`, i.e. `True`),
--     which typechecks only if two independent parameters reached
--     registration. A written parameter is DECLARED and heads the list, so the
--     order is `.{u_0, β}`. Measured 2026-08-26b on the release binary,
--     `--prelude builtin`: the one-argument form `@idCollide.{1}` reports
--     `UniverseLevelMismatch { name: "idCollide", expected: 2, actual: 1 }`,
--     and `.{0, 1}` (the levels swapped) is refused with
--     `universe level conflict: 0 vs 1`.
def useIdCollide : Nat := @idCollide.{1, 0} True True.intro Nat 4

-- 2. A level HOLE on its own. Holes route through `fresh_universe_param` and
--    must stay SOLVABLE — the fix classifies minted names, it does not make
--    them rigid. Its generalized parameter is still spelled `u_1`: the
--    reservation moved the METAVARIABLE spelling, not the interface one.
def holeOnly (β : Sort _) (x : β) : β := x

-- 3. A written `u_1` with no mint anywhere in the declaration: the ordinary
--    auto-bound path, which was already correct.
def noMintCollision (γ : Sort u_1) (y : γ) : γ := y

-- 4. A DECLARED `.{u_2}`. `set_decl_universe_params` installs it rigid before
--    any mint runs, so the mint skip-loop already protected this shape; it is
--    here so a future change to that loop cannot pass unnoticed.
def declaredCollision.{u_2} (γ : Sort u_2) (y : γ) : γ := y

-- 4b. THE GUILLEMET CONTROL for p51 (2026-08-26b). p51 refuses a written
--     universe name inside the reserved metavariable space, and a guillemet
--     identifier is the only way to write one — so p51 alone cannot tell
--     "the `?`-LEADING space is reserved" from the over-broad "guillemet
--     universe names are rejected" or "a `?` anywhere in a universe name is
--     rejected". This name contains a `?` and arrives through `«…»`, and it
--     must keep elaborating. (It did at `2ce2cf2c1`, before the reservation
--     existed: `1 passed, 0 failed`.)
def guillemetUniverse (γ : Sort «my?weird») (y : γ) : γ := y

-- 5. p49's RENAME CONTROL. Exactly p49's `n3` with the written universe
--    renamed `u_0` -> `w`. It passed before the namespace was reserved and
--    passes now; `n3` used to be the line that failed. `l : List β` forces
--    `β : Type _` and the two universes stay independent — Lean's verdict, and
--    Clean's. If this one ever fails, a refusal at `n3` has stopped being
--    about the spelling and is about the shape instead.
def nonCollidingForcedHole (β : Sort _) (γ : Sort w) (y : γ) (l : List β) : Nat := 0

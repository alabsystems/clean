-- P49 — a level HOLE and a written universe are INDEPENDENT universes, at
-- every spelling. FLIPPED 2026-08-26b from a MUST_FAIL cost pin to a positive
-- pin, and renamed from `p49_mint_collision_overconstraint_MUST_FAIL.lean` —
-- the old name states a behaviour that has gone away.
--
-- U2 stage-3 deferral 1, follow-up route "reserve the mint namespace"
-- (`data/u2_stage3_deferrals.PENDING.md`, "Follow-up this work NAMES but does
-- not do"). The flip target that ledger designated is this file.
--
-- WHAT THIS FIXTURE USED TO PIN, and why it is gone rather than relaxed.
--
-- p47 (2026-08-26a) closed a silent monomorphization: a user-WRITTEN universe
-- name that collided with a name its own declaration had already minted read
-- as "already a parameter", never became rigid, and was solved away. The cure
-- was to classify the name by ROLE (`crate::level_role`) and promote a written
-- one to rigid. That closed the silent half and PAID a measured cost, pinned
-- here: because level identity is `Level::Param(Name)`, promoting resolved the
-- clash by making BOTH occurrences one rigid level, so a declaration whose two
-- universes must be INDEPENDENT was refused —
--
--   def n3 (β : Sort _) (γ : Sort u_0) (y : γ) (l : List β) : Nat := 0
--     -- cannot assign rigid universe parameter u_0 := u_1 + 1
--
-- — while the same declaration spelled `Sort w` was accepted. Lean accepts
-- both. The verdict depended on the SPELLING; p47 only changed its direction,
-- silent to loud.
--
-- THE FIX IS THE NAMESPACE, NOT THE SOLVER. Universe metavariables are now
-- minted into a RESERVED space the surface grammar cannot produce — `?u_0`,
-- `?u_1`, … (`crate::level_mint::MINT_PREFIX`; `?` is not an
-- identifier-start character, and the one door that bypasses the lexer's
-- identifier rules, a guillemet identifier `Sort «?u_0»`, is refused by
-- `elab_level` with `ReservedUniverseName`). A written name and a minted one
-- therefore inhabit DISJOINT spellings, so the collision that produced both
-- the p47 defect and this file's cost cannot be constructed at all. Nothing
-- about rigidity, unification or the level solver changed, and no kernel
-- representation moved: `clean_kernel::Level` still has `Param(Name)` and no
-- metavariable constructor.
--
-- The names the user SEES did not move either. A mint that survives to
-- declaration close is renamed into the writable space by
-- `finalize_level_params` (Lean's `levelMVarToParam`) through
-- `ElabCtx::fresh_generalized_universe_param`, which draws from the SAME
-- counter — so `def holeOnly (β : Sort _) (x : β) : β := x` registered `u_1`
-- at `2ce2cf2c1` and registers `u_1` here.
--
-- WHAT IS PINNED BELOW, and in what weight.
--
-- The three spellings, and — in equal weight — an ARITY witness for each.
-- "It elaborates" is not the claim: a declaration whose two universes were
-- conflated into one also elaborates, and would have registered ONE parameter.
-- Each use site instantiates its declaration at two DIFFERENT levels, which
-- only typechecks if two independent parameters survived. Measured on the
-- release binary, `--prelude builtin`, 2026-08-26b: with a single argument
-- `@n3.{0}` reports `UniverseLevelMismatch { name: "n3", expected: 2,
-- actual: 1 }`, so the arity really is two.
--
-- p47 stays a MUST_FAIL and must keep failing IDENTICALLY: `Sort u_0 := Nat`
-- monomorphizes a universe the source declares whatever else is minted, and
-- reserving the namespace must not have relaxed that. p48 is the precision
-- companion, where `idCollide` now carries the second universe parameter this
-- file's header used to say it could not have.

-- 1. Both universes are HOLES. This spelling always passed; it is the floor
--    the other two now meet. `l : List β` forces `β : Type _`, so the two
--    levels are genuinely different things and not merely two names.
--    Generalized in FIRST-USE order (β, then γ), hence `.{0, 1}`.
def n3h (β : Sort _) (γ : Sort _) (y : γ) (l : List β) : Nat := 0

def useN3h : Nat := @n3h.{0, 1} Nat Nat 3 (@List.nil Nat)

-- 2. The RENAME control: one hole, one written universe whose name could never
--    collide with a mint. This passed before the namespace was reserved and
--    passes now — it is the line that proves the flip below is about the
--    collision and not about the shape. (It also lives in p48 as
--    `nonCollidingForcedHole`, where it guards p47's precision.)
--    A written parameter is DECLARED, so it heads the list: `.{w, β}`.
def n3w (β : Sort _) (γ : Sort w) (y : γ) (l : List β) : Nat := 0

def useN3w : Nat := @n3w.{1, 0} Nat Nat 3 (@List.nil Nat)

-- 3. THE FLIP. Byte-identical to shape 2 with `w` renamed `u_0` — the spelling
--    that used to make the hole and the written parameter one rigid level and
--    turn the forcing constraint into
--    `cannot assign rigid universe parameter u_0 := u_1 + 1`.
--
--    Both the verdict AND the registered signature now agree with shape 2: the
--    same `.{1, 0}` instantiation typechecks against both, which is the whole
--    content of "the spelling no longer matters".
def n3 (β : Sort _) (γ : Sort u_0) (y : γ) (l : List β) : Nat := 0

def useN3 : Nat := @n3.{1, 0} Nat Nat 3 (@List.nil Nat)

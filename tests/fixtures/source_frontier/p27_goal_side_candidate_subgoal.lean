-- Updated 2026-11-06: Type _ supplies core Lean universe holes;
-- Type* without a Mathlib import is invalid Lean source. The parent projection
-- keeps its original implicit parameter form Pre.toLE. Both old Type* and
-- the experimentally over-applied parent projection remain recorded as
-- independent Clean false acceptances in the dated audit report.
-- p27 — CLASS I, FRONTIER STAGE I-2 at EVERY DEPTH: a CANDIDATE's own
-- Pi-shaped `[inst]` premise is answered by the goal-side telescope.
--
-- PROVES: `Pi.hasLe' : [∀ i, LE (π i)] → LE (∀ i, π i)` fires from instance
-- search when the only route to its premise is a telescope. `[∀ i, Pre (π i)]`
-- is in scope and `Pre extends LE`, so `LE (π i)` at an ARBITRARY `i` is
-- `fun i => Pre.toLE` — a term that has to be BUILT under the candidate.
--
-- MEASURED at HEAD 4996969f1 (2026-09-10, before the change): `target` fails
-- `failed to synthesize instance LE ((x : ι) -> π x)` while every other
-- declaration here passes — 8 passed, 1 failed. The `depth == 0` guard that
-- 307dc1afb (2026-08-28) put on `resolve_pi_goal_by_abstraction` refused the
-- abstraction for a candidate's sub-goal, which is not Lean's rule
-- (`SynthInstance.tryResolve` opens EVERY sub-goal with
-- `forallTelescopeReducing`). That guard is the mechanism behind the five
-- `Mathlib/Order/Basic.lean` regressions in
-- reports/source-elab/srcelab-2026-09-02-ge0b3ef7dd.json — `le_of_strongLT`,
-- `strongLT_of_strongLT_of_le`, `le_update_iff` and the two aliases
-- downstream of them — and behind seven more `LE`/`LT (∀ i, π i)` refusals in
-- that file that had reached their tactic proofs on 2026-08-31.
--
-- IN-FILE CONTROLS, each one LINK of the chain on its own, passing before and
-- after:
--   * `viaLE`        the premise's shape with a matching local
--                    `[∀ i, LE (π i)]`: candidate-side match (stage I-1), no
--                    telescope needed.
--   * `localOnly`    the telescoped local: `Pre (π i)` at a given `i`.
--   * `oneLink`      the telescoped local through the parent projection.
--   * `depthZero`    `∀ i, LE (π i)` as the ELABORATOR's goal — stage I-2 at
--                    depth 0, the half that always worked.
--   * `explicitHead` `Pi.hasLe'` named, its premise synthesized as an
--                    inst-implicit ARGUMENT (also depth 0).
--   * `explicit`     the fully spelled term, so the target is inhabited.
-- So what `target` measures is exactly the depth: the same premise, asked one
-- level down.
--
-- CONTROL: p25/p26 — the two refusals INSIDE the abstraction (arbitrary
-- argument, arity cap) are untouched by the depth change and still fail.
variable {ι : Type _} {π : ι → Type _}

instance Pi.hasLe' [∀ i, LE (π i)] : LE (∀ i, π i) where le x y := ∀ i, x i ≤ y i

class Pre (α : Type u) extends LE α where
  refl : ∀ a : α, a ≤ a

def viaLE [∀ i, LE (π i)] : LE (∀ i, π i) := inferInstance

def localOnly [∀ i, Pre (π i)] (i : ι) : Pre (π i) := inferInstance

def oneLink [∀ i, Pre (π i)] (i : ι) : LE (π i) := inferInstance

def depthZero [∀ i, Pre (π i)] : ∀ i, LE (π i) := inferInstance

def explicitHead [∀ i, Pre (π i)] : LE (∀ i, π i) := Pi.hasLe'

def explicit [∀ i, Pre (π i)] : LE (∀ i, π i) := @Pi.hasLe' _ _ (fun i => Pre.toLE)

def target [∀ i, Pre (π i)] : LE (∀ i, π i) := inferInstance

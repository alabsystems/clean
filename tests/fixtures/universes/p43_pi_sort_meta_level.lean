-- P43 — U2 stage 2: a Sort-typed metavariable assigned a PI TYPE gets its
-- level equation GENERATED (docs/analysis/u2-implementation-plan-2026-08-24.md
-- §3 stage 2, landed 2026-08-25).
--
-- `infer_level_for_type` handled Sort/FVar/Const/App and fell through to
-- `None` on Pi, so `?A : Sort ?u := <function type>` never constrained `?u`
-- at all — no solver event (the CLEAN_U2_HISTOGRAM discriminator: the
-- equation was never generated, not mis-solved). The orphaned `?u` was then
-- GENERALIZED at declaration close and the mandatory kernel re-check refused
-- with the measured sub-class-B face:
--   `Kernel check failed for <name>: Type mismatch:
--      expected Sort(Param(u_N)), got Sort(Max(Succ(..), Succ(..)))`
-- (5-file source-elab gate at 369ba0951: Function.hasUncurryBase,
-- Set.SeparatesPoints, Pi.map_id — all class-adjacent, all with telescopes
-- wide enough to need `max`). Single-binder spellings never failed because
-- their assigned type is an FVar, which the lookup arm always handled.
--
-- Builtin-prelude repro, no Mathlib. Faces pinned here, all baseline-failing
-- except the two marked controls:
--   * hasUncurryBase — the recorded instance face byte-for-byte (section
--     variables + `⟨id⟩` over an `α → β` carrier; Max face).
--   * arrowId/sortArrowId/depPiId — Max, IMax, and dependent-Pi faces.
--   * propImpId — the Prop-codomain face (`got Sort(Zero)`).
--   * monoSolve — the new equation SOLVES through arms 7/9 when the
--     operands are assignable `Type*` mints (`max(u,v) := 0` — Lean accepts
--     this spelling as monomorphic too). Its rigid twin is p44.
--   * exfControl — in-family control: binder-ascribed Pi under `∃` passed
--     BEFORE the fix (app-path constraint generation) and must keep passing.

variable {α β γ : Type*}

class HasUncurry (α : Type*) (β : Type*) (γ : Type*) where
  uncurry : α → β → γ

instance hasUncurryBase : HasUncurry (α → β) α β :=
  ⟨id⟩

def arrowId {φ ψ : Type*} : (φ → ψ) → (φ → ψ) := id

def sortArrowId {φ ψ : Sort*} : (φ → ψ) → (φ → ψ) := id

def propImpId {p q : Prop} : (p → q) → (p → q) := id

def depPiId {ι : Type*} {δ : ι → Type*} : (∀ i, δ i) → (∀ i, δ i) := id

def exfControl {φ ψ : Type*} (A : (φ → ψ) → Prop) : Prop := ∃ f, A f

def tid (μ : Type) (c : μ) : μ := c

def monoSolve {φ ψ : Type*} (f : φ → ψ) : φ → ψ := tid _ f

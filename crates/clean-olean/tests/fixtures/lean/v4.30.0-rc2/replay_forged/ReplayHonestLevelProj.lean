prelude
import Init.Tactics

/-! `ReplayHonestLevelProj`: an elaborated proof whose kernel term holds a raw projection
`s.1` at `RhpS.{u, v, imax u v}` (the `delta` tactic unfolds `RhpS.y`), under
`Eq.refl.{..} (Sort (max (max u v) (imax u v)))`. Pinned Lean's kernel instantiates the
constructor's field sort `Sort (max (max a b) c)` with `instantiate_type_lparams` and admits it
(DECISIONS R150; the 2026-10-20 review's `HonestProjPrelude`). -/

universe u v

structure RhpS.{a, b, c} where
  y : Sort (max (max a b) c)

theorem rhp_c5 (s : RhpS.{u, v, imax u v}) : Eq (RhpS.y s) (RhpS.y s) := by
  delta RhpS.y
  exact Eq.refl _

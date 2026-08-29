/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

CAKE-GATE LAYER-2 REPRODUCER (core-only, no Mathlib).

A deliberately tiny theorem whose foundational closure pulls exactly the
constants implicated in the olean-lane cake-gate failures:
  * `Eq` / `Nat` / `Exists` inductive families (family-replay match), and
  * `propext` via `eq_true` (the "Unknown constant: propext" axiom-seeding gap).

Graduating this module through `--env olean` loads a ~core-sized closure in
SECONDS (not the ~90s Mathlib load), so the two layer-2 bugs can be diagnosed
and fixed with fast iteration. `#print axioms cake_repro` is `[propext]`.
-/
import Init

namespace Crownproof.CakeRepro

/-- Pulls `Exists` (∃), `Nat`, `Eq`, and `propext` (through `eq_true`). -/
theorem cake_repro : ∃ n : Nat, (n = n) = True :=
  ⟨0, eq_true rfl⟩

/-- Pulls `Classical.choice` (+ `Nonempty`): the second foundational axiom the
lean-core verify base must seed. `#print axioms` is `[Classical.choice]`. -/
theorem cake_repro_choice {α : Type} (h : Nonempty α) : Nonempty α :=
  ⟨Classical.choice h⟩

/-- Forces `Nat.rec` into the carried family closure (the family-recursor that
the smaller repros did not reference; Auto5's mathlib closure does). -/
def cake_repro_nat_rec : Nat → Nat :=
  fun n => Nat.rec 0 (fun _ ih => ih) n

/-- Forces `Exists.rec` (via `Exists.elim`) into the carried family closure. -/
theorem cake_repro_exists_rec {α : Type} (p : α → Prop) (h : ∃ x, p x) : True :=
  h.elim (fun _ _ => trivial)

end Crownproof.CakeRepro

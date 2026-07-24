import Lake
open Lake DSL

package «mathbot» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Mathbot where
  roots := #[`Mathbot, `Mathbot.Manifest]

lean_lib «Mathbot.FalseControls» where
  srcDir := "Mathbot"
  roots := #[`FalseControls]

-- HX (held-out) seed mini-domain and theorem statements.
-- Statements file contains only `sorry`-bodied theorems; the
-- canonical proofs live outside the public repo.
lean_lib «Mathbot.HX» where
  srcDir := "Mathbot"
  roots := #[`HX]

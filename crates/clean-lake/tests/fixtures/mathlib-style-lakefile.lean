import Lake

open Lake DSL

/-!
## Mathlib-style lakefile fixture

A checked-in, Mathlib-shaped `lakefile.lean` exercising strict-parse
diagnostics: the declarative subset (require / package / lean_lib / lean_exe)
parses, and the top-level `abbrev` declarations are the exact constructs the
simplified parser must account for instead of dropping silently.
-/

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "master"
require "leanprover-community" / "aesop" @ git "master"
require "leanprover-community" / "plausible" @ git "main"

/-- These options are enabled for Mathlib files only. -/
abbrev mathlibOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩
]

/-- These options are passed to all Mathlib builds. -/
abbrev mathlibLeanOptions := mathlibOnlyLinters ++ #[⟨`pp.unicode.fun, true⟩]

package mathlib where
  testDriver := "MathlibTest"

/-!
## Definition and configuration of `Mathlib`
-/

@[default_target]
lean_lib Mathlib where
  leanOptions := mathlibLeanOptions

lean_lib Cache

lean_lib MathlibTest where
  globs := #[.submodules `MathlibTest]

/-- `lake exe autolabel 150100` adds a topic label to PR `150100`. -/
lean_exe autolabel where
  srcDir := "scripts"

/-- `lake exe cache get` downloads precompiled build artifacts. -/
lean_exe cache where
  root := `Cache.Main

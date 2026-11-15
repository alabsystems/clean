/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

The generator of Clean's table of Lean 4.8.0's `Init` export aliases
(`export LawfulMonad (bind_assoc …)` makes `bind_assoc` a name a Lean file
with no `import` line can write, though no CONSTANT is called that). Run it
with the pinned Lean only through `scripts/gen_lean_core_alias_table.sh`,
which writes `init_aliases_v4.8.0.txt` with its digests;
`crates/clean-elab/src/lean_core_names.rs` checks them and runs this again.

    lean --run DumpInitAliases.lean <aliases-out>

It builds the environment of a Lean file with no `import` line exactly as
`DumpLeanCore.lean` does and writes every alias name of `aliasExtension`,
sorted by `String.lt`, one per line. An alias whose name `Name.toString`
would escape aborts the run rather than being written ambiguously.

The first line printed on stdout is `lean <version> <githash>`.
-/
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let [aliasesOut] := args
    | throw (IO.userError "usage: lean --run DumpInitAliases.lean <aliases-out>")
  let some sysroot := (← IO.appDir).parent
    | throw (IO.userError "cannot locate the Lean sysroot from the running binary")
  initSearchPath sysroot
  let env ← importModules #[{ module := `Init }] {} 0
  let mut names : Array String := #[]
  for (a, _) in (aliasExtension.getState env).toList do
    let s := a.toString (escape := false)
    if s.any (fun c => c == '«' || c == '»' || c.isWhitespace) || a.hasNum then
      throw (IO.userError s!"alias {a} cannot be written")
    names := names.push s
  let sorted := names.qsort (· < ·)
  IO.FS.writeFile aliasesOut (String.join (sorted.toList.map (· ++ "\n")))
  IO.println s!"lean {Lean.versionString} {Lean.githash}"

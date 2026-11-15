/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

The generator of Clean's table of the `protected` names of Lean 4.8.0's
`Init`: every constant marked `protected`, and every `export` alias all of
whose targets are. Lean's `resolveQualifiedName` never reaches such a name
from an ATOMIC identifier through a namespace (`open Nat in … pow_succ` is an
unknown identifier although `Nat.pow_succ` exists). Run it with the pinned
Lean only through `scripts/gen_lean_core_protected_table.sh`, which writes
`init_protected_v4.8.0.txt` with its digests;
`crates/clean-elab/src/lean_core_names.rs` checks them and runs this again.

    lean --run DumpInitProtected.lean <protected-out>

Names are written in the component syntax of `DumpLeanCore.lean` (the
constants table's), sorted by `String.lt`, one per line.

The first line printed on stdout is `lean <version> <githash>`.
-/
import Lean
open Lean

def plainComponent (s : String) : Bool :=
  !s.isEmpty && !s.all Char.isDigit && !s.startsWith "#" &&
    !s.any (fun c => c == '.' || c == '«' || c == '»' || c.isWhitespace)

def writeComponent : Name → Except String String
  | .str _ s =>
    if s.any (fun c => c == '»' || c == '\n' || c == '\r') then
      .error s!"component {repr s} cannot be written"
    else if plainComponent s then .ok s
    else .ok ("«" ++ s ++ "»")
  | .num _ n => .ok (toString n)
  | .anonymous => .error "anonymous component"

partial def writeName (n : Name) : Except String String := do
  match n with
  | .anonymous => .error "anonymous name"
  | .str .anonymous _ | .num .anonymous _ => writeComponent n
  | .str p _ | .num p _ => return (← writeName p) ++ "." ++ (← writeComponent n)

def main (args : List String) : IO Unit := do
  let [protectedOut] := args
    | throw (IO.userError "usage: lean --run DumpInitProtected.lean <protected-out>")
  let some sysroot := (← IO.appDir).parent
    | throw (IO.userError "cannot locate the Lean sysroot from the running binary")
  initSearchPath sysroot
  let env ← importModules #[{ module := `Init }] {} 0
  let mut names : Array String := #[]
  for (n, _) in env.constants.toList do
    if isProtected env n then
      match writeName n with
      | .ok s => names := names.push s
      | .error e => throw (IO.userError s!"constant {n}: {e}")
  for (a, targets) in (aliasExtension.getState env).toList do
    if !targets.isEmpty && targets.all (isProtected env) && !env.contains a then
      match writeName a with
      | .ok s => names := names.push s
      | .error e => throw (IO.userError s!"alias {a}: {e}")
  let sorted := names.qsort (· < ·)
  for i in [1:sorted.size] do
    if sorted[i-1]! == sorted[i]! then
      throw (IO.userError s!"two names are written {sorted[i]!}")
  IO.FS.writeFile protectedOut (String.join (sorted.toList.map (· ++ "\n")))
  IO.println s!"lean {Lean.versionString} {Lean.githash}"

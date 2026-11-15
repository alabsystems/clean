/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

The generator of Clean's two tables of Lean 4.8.0 core facts. Run it with the
pinned Lean ONLY through `scripts/gen_lean_core_tables.sh`, which writes both
tables with their digests; `crates/clean-elab/tests/lean_core_tables.rs` runs
it again and fails if a committed table differs from what it prints.

    lean --run DumpLeanCore.lean <constants-out> <keywords-out>

It builds the environment of a Lean file with no `import` line and no
`prelude` (such a file imports `Init`, and nothing else), exactly as the
frontend does, and writes:

* `<constants-out>`: every constant of that environment — the names a user
  declaration cannot take (`Lean.Elab.checkNotAlreadyDeclared`: "'x' has
  already been declared"). Nothing is filtered: internal, auxiliary and
  private names are constants of the environment like any other.
* `<keywords-out>`: every token of that environment's token table that is
  spelled like an identifier (`Lean.isIdFirst` then `Lean.isIdRest`). Lean's
  identifier scanner turns such a spelling into the keyword, never an
  identifier (`Lean.Parser.identFnAux`, `mkIdResult`: a token at least as
  long as the identifier wins), so it can be neither a binder nor a name.

Both are sorted by `String.lt` (code point order, which is also UTF-8 byte
order), one entry per line. A name is written component by component,
separated by `.`: a numeric component (`Name.num`) as its decimal digits; a
string component verbatim when it is non-empty, not all decimal digits, does
not begin with `#` (a table's header lines do), and contains none of `.`,
`«`, `»` or whitespace, and otherwise inside `«»`. A
component that `«»` cannot carry (it contains `»` or a line break) aborts the
run rather than being written ambiguously.

The first line printed on stdout is `lean <version> <githash>` of the Lean
that ran.
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
  | .anonymous => .error "anonymous constant name"
  | .str .anonymous _ | .num .anonymous _ => writeComponent n
  | .str p _ | .num p _ => return (← writeName p) ++ "." ++ (← writeComponent n)

def identLike (t : String) : Bool :=
  match t.toList with
  | c :: cs => Lean.isIdFirst c && cs.all Lean.isIdRest
  | [] => false

def writeLines (path : String) (lines : Array String) : IO Unit :=
  IO.FS.writeFile path (String.join (lines.toList.map (· ++ "\n")))

def main (args : List String) : IO Unit := do
  let [constantsOut, keywordsOut] := args
    | throw (IO.userError "usage: lean --run DumpLeanCore.lean <constants-out> <keywords-out>")
  let some sysroot := (← IO.appDir).parent
    | throw (IO.userError "cannot locate the Lean sysroot from the running binary")
  initSearchPath sysroot
  let env ← importModules #[{ module := `Init }] {} 0
  let mut names : Array String := #[]
  for (n, _) in env.constants.toList do
    match writeName n with
    | .ok s => names := names.push s
    | .error e => throw (IO.userError s!"constant {n}: {e}")
  let sorted := names.qsort (· < ·)
  for i in [1:sorted.size] do
    if sorted[i-1]! == sorted[i]! then
      throw (IO.userError s!"two constants are written {sorted[i]!}")
  let keywords := ((Lean.Parser.getTokenTable env).findPrefix "").filter identLike
  let keywords := keywords.qsort (· < ·)
  writeLines constantsOut sorted
  writeLines keywordsOut keywords
  IO.println s!"lean {Lean.versionString} {Lean.githash}"

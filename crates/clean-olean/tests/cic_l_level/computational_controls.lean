/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import Lean
open Lean

/-!
Pinned Lean's kernel on C1's computational controls. `cic_l_level.rs` runs this
with `lean --run`, `LEAN_PATH` naming the compiled theory and the pinned Lean
library, and one argument per control, `sound|Relation|kind|u|v`. Each becomes

  theorem CICL.Controls.<sound>_computational_<kind> : CICL.Level.<Relation> u v :=
    CICL.Level.<sound> u v (Eq.refl true)

handed to the kernel with checking on (`addDeclCore`, `doCheck := true`) over an
environment that imports `CICL.LevelDecideCases`, so no elaborator stands
between the term and the verdict. A level is words: the last is `p`, `q` or
`zero` and each one before it is `succ`. This program prints the kernel's
verdict per control and decides nothing: the test holds the expected verdicts.
-/

def level : List String → Except String Expr
  | ["p"] => pure (mkConst `CICL.LevelDecideCases.p)
  | ["q"] => pure (mkConst `CICL.LevelDecideCases.q)
  | ["zero"] => pure (mkConst `CICL.Level.zero)
  | "succ" :: rest => return mkApp (mkConst `CICL.Level.succ) (← level rest)
  | words => throw s!"bad level {words}"

def trueRefl : Expr :=
  mkApp2 (mkConst `Eq.refl [Level.one]) (mkConst `Bool) (mkConst `Bool.true)

def controlDecl (line : String) : Except String (String × Declaration) := do
  let [sound, relation, kind, u, v] := line.splitOn "|" | throw s!"bad control {line}"
  let u ← level (u.splitOn " ")
  let v ← level (v.splitOn " ")
  let name := (`CICL.Controls).str s!"{sound}_computational_{kind}"
  let type := mkApp2 (mkConst ((`CICL.Level).str relation)) u v
  let value := mkApp3 (mkConst ((`CICL.Level).str sound)) u v trueRefl
  return (s!"{sound} {kind}", .thmDecl { name, levelParams := [], type, value, all := [name] })

def main (args : List String) : IO UInt32 := do
  let some sysroot := (← IO.appDir).parent | return 2
  initSearchPath sysroot
  let env ← importModules #[{ module := `CICL.LevelDecideCases }] {} (trustLevel := 0)
  for line in args do
    let (label, decl) ← IO.ofExcept (controlDecl line)
    match env.addDeclCore 0 decl none (doCheck := true) with
    | .ok _ => IO.println s!"C1 pinned Lean kernel {label}: accepted"
    | .error (.appTypeMismatch ..) =>
      IO.println s!"C1 pinned Lean kernel {label}: refused, application type mismatch"
    | .error e =>
      IO.println s!"C1 pinned Lean kernel {label}: refused otherwise: {← (e.toMessageData {}).toString}"
  return 0

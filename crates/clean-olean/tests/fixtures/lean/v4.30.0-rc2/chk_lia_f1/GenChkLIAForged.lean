import Lean

/-!
# `GenChkLIAForged` — the quorum's negative control and its positive twin

A `lean --run` GENERATOR, not a module source:

    lean --run GenChkLIAForged.lean <out.olean> forged|honest

Both import `ChkLIAF1` and `ChkLIASpec` (compiled before this step, found through
`LEAN_PATH`; so one load of either reaches the whole theory and the corpus) and add one
theorem built from `ChkLIAF1.f1_025`'s type and its own `rfl` proof, then write the module
with Lean's serializer:

* `forged` (`ChkLIAForged`): `f1_025_false : chk_LIA_cases … = false`, added with
  `doCheck := false`, so the `.olean` carries a declaration Lean's kernel never admitted.
  Kernel evaluation of the VF4 checker gives `true`: every member of the quorum must refuse.
* `honest` (`ChkLIAHonest`): `f1_025_true`, the same statement with `true`, added with
  `doCheck := true`: every member must accept it.

`crates/clean-olean/tests/vf4_chk_lia_quorum.rs` reads both. Exit status: 0 on success,
2 on a usage error, 1 when the checked declaration is rejected.
-/

open Lean

def flipRhs (ty : Expr) (b : Name) : Option Expr :=
  match ty.getAppFn, ty.getAppArgs with
  | .const ``Eq ls, #[α, lhs, _] => some (mkApp3 (.const ``Eq ls) α lhs (.const b []))
  | _, _ => none

def main (args : List String) : IO UInt32 := do
  let (out, mode) ← match args with
    | [out, mode] => pure (out, mode)
    | _ =>
      IO.eprintln "usage: lean --run GenChkLIAForged.lean <out.olean> forged|honest"
      return (2 : UInt32)
  let (modName, thmName, rhs, checked) ← match mode with
    | "forged" => pure (`ChkLIAForged, `ChkLIAForged.f1_025_false, ``Bool.false, false)
    | "honest" => pure (`ChkLIAHonest, `ChkLIAHonest.f1_025_true, ``Bool.true, true)
    | _ =>
      IO.eprintln s!"unknown mode `{mode}`"
      return (2 : UInt32)
  try
    let some sysroot := (← IO.appDir).parent
      | throw <| IO.userError "cannot locate the Lean sysroot from IO.appDir"
    initSearchPath sysroot
    let env ← importModules #[{ module := `ChkLIAF1 }, { module := `ChkLIASpec }] {}
      (trustLevel := 0)
    let env := env.setMainModule modName
    let some (.thmInfo c) := env.find? `ChkLIAF1.f1_025
      | throw <| IO.userError "ChkLIAF1.f1_025 is not a theorem of ChkLIAF1"
    let value := c.value
    let some ty := flipRhs c.type rhs
      | throw <| IO.userError "ChkLIAF1.f1_025 is not `@Eq Bool lhs rhs`"
    let decl := Declaration.thmDecl { name := thmName, levelParams := [], type := ty, value }
    match env.addDeclCore 0 decl none (doCheck := checked) with
    | .ok env => writeModule env out; return (0 : UInt32)
    | .error ex =>
      let msg ← (ex.toMessageData {}).toString
      IO.eprintln s!"GenChkLIAForged: the kernel rejected the {mode} declaration: {msg}"
      return (1 : UInt32)
  catch e =>
    IO.eprintln s!"GenChkLIAForged: {e}"
    return (1 : UInt32)

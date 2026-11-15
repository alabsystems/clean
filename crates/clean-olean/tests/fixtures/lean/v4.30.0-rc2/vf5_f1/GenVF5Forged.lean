import Lean

/-!
# `GenVF5Forged` — the quorum's negative control for VF5 and its positive twin

A `lean --run` GENERATOR, not a module source:

    lean --run GenVF5Forged.lean <out.olean> forged|honest

Both import `VF5Spec` (the family's root, compiled before this step, found through
`LEAN_PATH`) and add one theorem built from `VF5Rows.checks_collision`'s type and its own
`rfl` proof, then write the module with Lean's serializer:

* `forged` (`VF5Forged`): `checks_false : checkBlob blob_collision A_collision
  certs_collision = false` — the row's verdict flipped — added with `doCheck := false`,
  so the `.olean` carries a declaration Lean's kernel never admitted. Kernel evaluation
  gives `true`: every member of the quorum must refuse. (Flipping the verdict, not the
  annotation, keeps the refusal one evaluation: the proof's type and the forged type
  then differ only in the right-hand side, where a swapped annotation would send a
  kernel's lazy unfolding through both checks in lockstep.)
* `honest` (`VF5Honest`): `checks_again`, `checks_collision`'s own statement, added with
  `doCheck := true`: every member must accept it.

`crates/clean-olean/tests/vf5_f1_reference.rs` reads both. Exit status: 0 on success,
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
      IO.eprintln "usage: lean --run GenVF5Forged.lean <out.olean> forged|honest"
      return (2 : UInt32)
  let (modName, thmName, forge, checked) ← match mode with
    | "forged" => pure (`VF5Forged, `VF5Forged.checks_false, true, false)
    | "honest" => pure (`VF5Honest, `VF5Honest.checks_again, false, true)
    | _ =>
      IO.eprintln s!"unknown mode `{mode}`"
      return (2 : UInt32)
  try
    let some sysroot := (← IO.appDir).parent
      | throw <| IO.userError "cannot locate the Lean sysroot from IO.appDir"
    initSearchPath sysroot
    let env ← importModules #[{ module := `VF5Spec }] {} (trustLevel := 0)
    let env := env.setMainModule modName
    let some (.thmInfo c) := env.find? `VF5Rows.checks_collision
      | throw <| IO.userError "VF5Rows.checks_collision is not a theorem of VF5Rows"
    let ty ← if forge then
        match flipRhs c.type ``Bool.false with
        | some t => pure t
        | none => throw <| IO.userError "checks_collision is not `@Eq Bool lhs rhs`"
      else pure c.type
    let decl := Declaration.thmDecl { name := thmName, levelParams := [], type := ty, value := c.value }
    match env.addDeclCore 0 decl none (doCheck := checked) with
    | .ok env => writeModule env out; return (0 : UInt32)
    | .error ex =>
      let msg ← (ex.toMessageData {}).toString
      IO.eprintln s!"GenVF5Forged: the kernel rejected the {mode} declaration: {msg}"
      return (1 : UInt32)
  catch e =>
    IO.eprintln s!"GenVF5Forged: {e}"
    return (1 : UInt32)

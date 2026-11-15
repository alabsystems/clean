import Lean

/-!
# `GenP3Planted` — the planted proof of `False` of the patched-kernel control

A `lean --run` GENERATOR, not a module source:

    lean --run GenP3Planted.lean <out.olean> <family>

Unit P3 of the kernel self-proof plan (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`)
asks whether a `clean-kernel` that accepts a planted proof of `False` yields an accepted row.
The planted pair is the closed, axiom-free, ill-typed term `Nat.zero` at type `False`; the
mutant built by `scripts/patched_kernel_control.py` accepts exactly that pair.

* `planted` writes `P3Planted.olean`: `theorem planted : False := Nat.zero` over
  `Init.Prelude`, added with `doCheck := false` (the kernel bypass of
  `set_option debug.skipKernelTC true`), so the `.olean` carries a declaration Lean's
  kernel never admitted.
* `honest` writes `P3Honest.olean`: `theorem p3_honest : True := True.intro`, added with
  `doCheck := true`, the non-vacuity control every lane must admit.

Both are written by `Lean.writeModule`, the serializer behind every stdlib `.olean`.

Exit status: 0 on success, 2 on a usage error, 1 when a CHECKED declaration is rejected.
-/

open Lean

def cnst (n : Name) : Expr := .const n []

/-- (main module, checked?, declarations in `addDecl` order), each over `Init.Prelude`. -/
def family : String → Option (Name × Bool × Array Declaration)
  | "planted" => some (`P3Planted, false, #[
      .thmDecl { name := `planted, levelParams := [], type := cnst ``False,
                 value := cnst ``Nat.zero }])
  | "honest" => some (`P3Honest, true, #[
      .thmDecl { name := `p3_honest, levelParams := [], type := cnst ``True,
                 value := cnst ``True.intro }])
  | _ => none

def generate (out : System.FilePath) (fam : String) : IO UInt32 := do
  -- The toolchain's own stdlib, found from the running binary (never from `PATH`).
  let some sysroot := (← IO.appDir).parent
    | throw <| IO.userError "cannot locate the Lean sysroot from IO.appDir"
  initSearchPath sysroot
  let some (mod, checked, decls) := family fam
    | IO.eprintln s!"unknown family `{fam}`"; return 2
  let mut env ← importModules #[{ module := `Init.Prelude }] {} (trustLevel := 0)
  env := env.setMainModule mod
  for d in decls do
    match env.addDeclCore 0 d none (doCheck := checked) with
    | .ok next => env := next
    | .error ex =>
      let msg ← (ex.toMessageData {}).toString
      throw <| IO.userError s!"kernel rejected a {if checked then "checked" else "planted"} declaration: {msg}"
  writeModule env out
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [out, fam] =>
    try
      generate out fam
    catch e =>
      IO.eprintln s!"GenP3Planted: {e}"
      return (1 : UInt32)
  | _ =>
    IO.eprintln "usage: lean --run GenP3Planted.lean <out.olean> (planted|honest)"
    return 2

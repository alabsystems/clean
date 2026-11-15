import Lean

/-!
# `GenNumericProbe` — mint the NumericProbe `.olean` fixtures with Lean's own serializer

Numeric `Name` components (`Name.num p 0`, `Name.num p 7`, …) cannot be spelled in
Lean surface syntax, so this file is a GENERATOR rather than a module source:

    lean --run GenNumericProbe.lean <out.olean>              -- six supported names
    lean --run GenNumericProbe.lean <out.olean> --over-u64   -- the six plus `Name.num p (2^64)`

It builds an import-free environment (`importModules #[]`), names the main module
`NumericProbe`, kernel-checks one `def <name> : Sort 1 := Sort 0` per name through
`Environment.addDeclCore` (Lean's own kernel; `doCheck := true`), and writes the
result with `writeModule` — the same serializer that writes every stdlib `.olean`.
The output has `imports = #[]`, so a loader needs no dependency closure to read it.

The six supported names are exactly the set `typed_import_identity.rs` and
`typed_cached_identity.rs` enumerate; `2^63` is a one-limb `mpz` in the compacted
region (it does not fit Lean's 63-bit boxed scalar), and `2^64` is a two-limb `mpz`
that a `u64`-carrying reader must refuse rather than truncate.

Exit status: 0 on success, 2 on a usage error, 1 when the kernel rejects a
declaration (the kernel message is printed to stderr).
-/

open Lean

/-- The names, in declaration order. `2^63` and `2^64` are `Nat` literals: Lean's
`Name.num` takes a `Nat`, so no 64-bit wraparound is possible here. -/
def probeNames (overU64 : Bool) : Array Name :=
  let p := `NumericProbe
  let supported : Array Name :=
    #[.num p 0, .num p 7, .num p (2 ^ 63), .str p "0", .str p "7", .str p "07"]
  if overU64 then supported.push (.num p (2 ^ 64)) else supported

/-- `def <n> : Sort 1 := Sort 0`, i.e. `: Type := Prop` — the shape the consuming tests
assert (`type_ == Expr::type_()`, `value == Some(Expr::prop())`). -/
def probeDecl (n : Name) : Declaration :=
  .defnDecl {
    name := n
    levelParams := []
    type := .sort (.succ .zero)
    value := .sort .zero
    hints := .abbrev
    safety := .safe
  }

def generate (out : System.FilePath) (overU64 : Bool) : IO Unit := do
  let mut env ← importModules #[] {} (trustLevel := 0)
  env := env.setMainModule `NumericProbe
  for n in probeNames overU64 do
    match env.addDeclCore 0 (probeDecl n) none with
    | .ok next => env := next
    | .error ex =>
      let msg ← (ex.toMessageData {}).toString
      throw <| IO.userError s!"kernel rejected {n}: {msg}"
  writeModule env out

def main (args : List String) : IO UInt32 := do
  let (out, overU64) ← match args with
    | [out] => pure (out, false)
    | [out, "--over-u64"] => pure (out, true)
    | _ =>
      IO.eprintln "usage: lean --run GenNumericProbe.lean <out.olean> [--over-u64]"
      return 2
  try
    generate out overU64
    return 0
  catch e =>
    IO.eprintln s!"GenNumericProbe: {e}"
    return 1

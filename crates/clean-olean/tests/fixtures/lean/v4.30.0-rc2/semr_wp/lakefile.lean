import Lake
import Lean.Elab.Import

open Lake DSL Lean

/- One package owns the existing pure files. The program-bound fixtures in
   this directory remain outside its roots and keep their existing ORDER. -/
package nativeContractCodec where
  version := v!"0.1.0"
  testDriver := "checkImports"

@[default_target]
lean_lib NativeContractCodec where
  roots := #[`NativeContractSyntax, `SemRBooleanClaim, `SemRBooleanClaimText]

private def codecImports : Array (String × Array Name) := #[
  -- The pinned 4.30 header includes both ordinary and meta Init imports.
  ("NativeContractSyntax", #[`Init, `Init]),
  ("SemRBooleanClaim", #[`Init, `Init, `NativeContractSyntax]),
  ("SemRBooleanClaimText", #[`Init, `Init, `SemRBooleanClaim])]

/-- Use Lean's own header parser; comments and malformed imports are not
    interpreted by a second source parser. The closed chain is Init-only. -/
private def importsMatch (source file : String) (expected : Array Name) : IO Bool := do
  let (imports, _, messages) ← Lean.Elab.parseImports source (some file)
  return !messages.hasErrors && imports.map (·.module) == expected

/-- Test the real source graph and hostile header mutations without importing
    another program model or changing any codec definition. -/
script checkImports do
  let root := (← getRootPackage).dir
  let mut controls := 0
  for (module, expected) in codecImports do
    let path := root / (module ++ ".lean")
    let source ← IO.FS.readFile path
    unless ← importsMatch source path.toString expected do
      throw <| IO.userError s!"pure contract codec: unexpected imports in {module}"
    controls := controls + 1
    for forbidden in ["SemR", "SemRBooleanWP", "SemRScalarClaim", "TrustIr.Semantics.Eval"] do
      if ← importsMatch ("import " ++ forbidden ++ "\n" ++ source) path.toString expected then
        throw <| IO.userError s!"pure contract codec: accepted {forbidden} in {module}"
      controls := controls + 1
    if ← importsMatch ("import (\n" ++ source) path.toString expected then
      throw <| IO.userError s!"pure contract codec: accepted a malformed import in {module}"
    controls := controls + 1
    unless ← importsMatch ("/- outer /- import SemR -/ import SemRBooleanWP -/\n" ++ source)
        path.toString expected do
      throw <| IO.userError s!"pure contract codec: confused a comment with an import in {module}"
    controls := controls + 1
  IO.println s!"pure contract codec: {codecImports.size} source roots, {controls} import controls passed"
  return 0

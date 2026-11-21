/-!
Reproduce the executable Char.ofNat implementation selected by a stable
non-module file with implicit Init. Run using Lean 4.36.0 with its own PATH.
-/
import Lean
import Lean.Compiler.IR.EmitUtil

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Init}] {} (loadExts := true)
  let mut work := #[`Char.ofNat]
  let mut seen : NameSet := {}
  let mut i := 0
  while i < work.size do
    let name := work[i]!
    i := i + 1
    if seen.contains name then continue
    seen := seen.insert name
    unless (Lean.Compiler.getImplementedBy? env name).isNone do
      throw (IO.userError s!"unexpected implementation override for {name}")
    let some owner := env.getModuleIdxFor? name | throw (IO.userError s!"no owner for {name}")
    let mod := env.header.modules[owner.toNat]!
    unless mod.module == `Init.Prelude && mod.irPhases == .all do
      throw (IO.userError s!"unexpected owner or phase of {name}")
    let some row := IR.findEnvDecl env name | throw (IO.userError s!"no declaration for {name}")
    let some selected := (IR.declMapExt.getModuleIREntries env owner).find? (·.name == name)
      | throw (IO.userError s!"no selected interpreter entry for {name}")
    unless toString row == toString selected && row.getInfo.sorryDep?.isNone do
      throw (IO.userError s!"unavailable runtime entry for {name}")
    IO.println row
    if let .extern (ext := attr) .. := row then
      match attr.entries with
      | [.standard backend symbol] => IO.println s!"{backend} {symbol}"
      | _ => throw (IO.userError s!"unsupported extern choices for {name}")
    work := work ++ ((IR.collectUsedDecls env [row]).filter (· != name))

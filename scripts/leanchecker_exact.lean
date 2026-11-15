/-
`leanchecker_exact` — `leanchecker`'s own replay of EXACTLY the named modules.

`leanchecker <M>` (`src/lean/LeanChecker.lean`, v4.30.0-rc2) replays every module `M` is a
dotted prefix of, all at once, as parallel tasks; on an internal module such as `Std` that is
hundreds of modules and several gigabytes, and its verdict is the conjunction over all of them.
`scripts/olean_replay_differential.py` needs a verdict per module, so this runs the function
`leanchecker` runs on each module — `replayFromImports`, copied below verbatim from
`LeanChecker.lean` — on exactly the modules named, one at a time, and prints one line each:

    EXACT <module> ok
    EXACT <module> fail <one-line message>

Run as `lean --run scripts/leanchecker_exact.lean <Module>...` with the toolchain the modules
were built by (the differential script uses the checkout's pinned one); `LEAN_PATH` supplies
the search path exactly as for `leanchecker`. Exit status: 0 when every module replayed, 1 when
any failed, 2 on a usage error. The differential compares this driver with `leanchecker` itself
on every module that has no submodule (where the two select the same module), and refuses any
disagreement between them.
-/
import Lean.CoreM
import Lean.Replay

open Lean

/-- `replayFromImports`, verbatim from `LeanChecker.lean` (v4.30.0-rc2). -/
unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    IO.eprintln "usage: lean --run scripts/leanchecker_exact.lean <Module>..."
    return 2
  let mut failed := false
  for arg in args do
    let mod := arg.toName
    try
      replayFromImports mod
      IO.println s!"EXACT {arg} ok"
    catch e =>
      failed := true
      let msg := (toString e).replace "\n" " | "
      IO.println s!"EXACT {arg} fail {msg}"
  return if failed then 1 else 0

import Lean
open Lean

/-!
# Per-module IR census oracle (pinned Lean side)

The pinned toolchain's own answer to "what compiled IR does each module of an
import closure carry?", in the exact row format `clean olean ir-census` prints,
so `scripts/ir_census_diff.py` can diff the two line by line.

Extended from the audit probe
`~/.cache/clean-lane/audit/metaprogramming/probes/IRCensus.lean` (which printed
per-PACKAGE sums) to one row per MODULE. The figures come from the same APIs:

* `fdecl_olean` / `extern_olean` — `IR.declMapExt.getModuleEntries env i`,
  i.e. the `Lean.IR.declMapExt` entries of the module's main data (the
  `.olean.private` part of a `module`, the `.olean` of a non-`module` file:
  `ImportedModule.mainModule?` in `Lean/Environment.lean`).
* `fdecl_ir` / `extern_ir` — `IR.declMapExt.getModuleIREntries env i`, the
  interpreter data (`ImportedModule.interpData?`): the `.ir` file of a `module`,
  the main data again for a non-`module` file.
* `extern_attr`, `implemented_by`, `regular_init`, `builtin_init` — the entry
  arrays of `Lean.externAttr`, `Lean.Compiler.implementedByAttr`,
  `Lean.regularInitAttr` and `Lean.builtinInitAttr` in the main data;
  `regular_init_ir` is `regularInitAttr`'s entries in the interpreter data
  (`exportIREntries`, `Lean/Compiler/IR/CompilerM.lean`, stores them in `.ir`).

This file must stay a standalone Lean program: the diff script inserts the
requested root imports directly after `import Lean`. `import Lean` itself only
provides the APIs used below; the census covers the transitive import closure of
`IR_CENSUS_ROOTS` (comma-separated module names), not of this file, so the extra
import never enlarges it.

`IR_CENSUS_OUT` (a path) writes the output to that file instead of stdout.

`IR_CENSUS_PRINT` (comma-separated declaration names, compared against
`toString decl.name`) additionally prints every matching IR declaration of the
closure, framed as `DECL <module> <olean|ir> <name>` … `ENDDECL`, with Lean's own
`IR.Decl` formatter (`declToString`, `Lean/Compiler/IR/Format.lean`).

`IR_CENSUS_PRINT_MODULES` (comma-separated module names, or `*` for every
module of the closure) prints EVERY IR declaration of those modules the same
way — the whole-module structural diff.

`IR_CENSUS_ATTRS=1` additionally prints, per module of the closure, every entry
of the four attributes and the data the IR itself carries outside its body:

```text
ATTR <module> extern <decl> <entries>
ATTR <module> implemented_by <decl> <target>
ATTR <module> regular_init <decl> <initFn>
ATTR <module> regular_init_ir <decl> <initFn>
ATTR <module> builtin_init <decl> <initFn>
DECLEXT <module> <olean|ir> <decl> <entries>      -- every `Decl.extern`
DECLSORRY <module> <olean|ir> <decl> <sorryDep>   -- every `DeclInfo.sorryDep? = some _`
```

`<entries>` renders `ExternAttrData.entries` as `adhoc <b>`, `inline <b> "<p>"`,
`standard <b> "<f>"`, `opaque`, joined by ` | ` (`none` when empty).
-/

namespace IRCensusOracle

def countIR (ds : Array IR.Decl) : Nat × Nat :=
  ds.foldl (init := (0, 0)) fun (f, e) d =>
    match d with
    | .fdecl .. => (f + 1, e)
    | .extern .. => (f, e + 1)

def fmtEntry : ExternEntry → String
  | .adhoc b => s!"adhoc {b}"
  | .inline b p => s!"inline {b} {p.quote}"
  | .standard b f => s!"standard {b} {f.quote}"
  | .opaque => "opaque"

def fmtEntries (d : ExternAttrData) : String :=
  if d.entries.isEmpty then "none" else " | ".intercalate (d.entries.map fmtEntry)

def splitList (s : String) : List String :=
  (s.splitOn ",").filterMap fun t =>
    let t := t.trimAscii.toString
    if t.isEmpty then none else some t

/-- Transitive import closure of `roots`, as module indices. -/
def closure (env : Environment) (roots : List Name) : IO (Array Nat) := do
  let names := env.header.moduleNames
  let mut idxOf : Std.HashMap Name Nat := {}
  for i in [0:names.size] do
    idxOf := idxOf.insert names[i]! i
  let mut seen : Std.HashSet Nat := {}
  let mut work : Array Nat := #[]
  for r in roots do
    match idxOf[r]? with
    | some i => work := work.push i
    | none => throw <| IO.userError s!"root module {r} is not in the environment"
  while !work.isEmpty do
    let i := work.back!
    work := work.pop
    if seen.contains i then continue
    seen := seen.insert i
    for imp in env.header.moduleData[i]!.imports do
      match idxOf[imp.module]? with
      | some j => work := work.push j
      | none => throw <| IO.userError s!"import {imp.module} of {names[i]!} is not in the environment"
  return seen.toArray

unsafe def main : CoreM Unit := do
  -- `#eval` captures what `IO.println` writes and replays it as one message at
  -- the end, which holds the whole output in memory; a whole-closure run with
  -- every declaration rendered is hundreds of megabytes, so `IR_CENSUS_OUT`
  -- sends it to a file handle instead.
  let out ← match (← IO.getEnv "IR_CENSUS_OUT") with
    | some path => IO.FS.Stream.ofHandle <$> IO.FS.Handle.mk path .write
    | none => IO.getStdout
  let emit (line : String) : IO Unit := out.putStrLn line
  let env ← getEnv
  let names := env.header.moduleNames
  let roots := splitList ((← IO.getEnv "IR_CENSUS_ROOTS").getD "") |>.map String.toName
  let idxs ← if roots.isEmpty then pure (Array.range names.size) else closure env roots
  let idxs := idxs.qsort (fun a b => toString names[a]! < toString names[b]!)
  let mut tot : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0]
  for i in idxs do
    let (f1, e1) := countIR (IR.declMapExt.getModuleEntries env i)
    let (f2, e2) := countIR (IR.declMapExt.getModuleIREntries env i)
    let ext := (externAttr.ext.getModuleEntries env i).size
    let impl := (Compiler.implementedByAttr.ext.getModuleEntries env i).size
    let rinit := (regularInitAttr.ext.getModuleEntries env i).size
    let rinitIr := (regularInitAttr.ext.getModuleIREntries env i).size
    let binit := (builtinInitAttr.ext.getModuleEntries env i).size
    let row := #[f1, e1, f2, e2, ext, impl, rinit, rinitIr, binit]
    tot := (tot.zip row).map fun (a, b) => a + b
    emit s!"MOD {names[i]!} fdecl_olean={f1} extern_olean={e1} fdecl_ir={f2} extern_ir={e2} extern_attr={ext} implemented_by={impl} regular_init={rinit} regular_init_ir={rinitIr} builtin_init={binit}"
  emit s!"TOTAL modules={idxs.size} fdecl_olean={tot[0]!} extern_olean={tot[1]!} fdecl_ir={tot[2]!} extern_ir={tot[3]!} extern_attr={tot[4]!} implemented_by={tot[5]!} regular_init={tot[6]!} regular_init_ir={tot[7]!} builtin_init={tot[8]!}"
  let wanted := splitList ((← IO.getEnv "IR_CENSUS_PRINT").getD "")
  let wholeMods := splitList ((← IO.getEnv "IR_CENSUS_PRINT_MODULES").getD "")
  unless wanted.isEmpty && wholeMods.isEmpty do
    for i in idxs do
      let whole := wholeMods.contains "*" || wholeMods.contains (toString names[i]!)
      for (lvl, ds) in [("olean", IR.declMapExt.getModuleEntries env i),
                        ("ir", IR.declMapExt.getModuleIREntries env i)] do
        for d in ds do
          if whole || wanted.contains (toString d.name) then
            emit s!"DECL {names[i]!} {lvl} {d.name}"
            emit (toString d)
            emit "ENDDECL"
  if ((← IO.getEnv "IR_CENSUS_ATTRS").getD "") == "1" then
    for i in idxs do
      let m := names[i]!
      for (d, e) in externAttr.ext.getModuleEntries env i do
        emit s!"ATTR {m} extern {d} {fmtEntries e}"
      for (d, t) in Compiler.implementedByAttr.ext.getModuleEntries env i do
        emit s!"ATTR {m} implemented_by {d} {t}"
      for (d, t) in regularInitAttr.ext.getModuleEntries env i do
        emit s!"ATTR {m} regular_init {d} {t}"
      for (d, t) in regularInitAttr.ext.getModuleIREntries env i do
        emit s!"ATTR {m} regular_init_ir {d} {t}"
      for (d, t) in builtinInitAttr.ext.getModuleEntries env i do
        emit s!"ATTR {m} builtin_init {d} {t}"
      for (lvl, ds) in [("olean", IR.declMapExt.getModuleEntries env i),
                        ("ir", IR.declMapExt.getModuleIREntries env i)] do
        for d in ds do
          match d with
          | .extern f _ _ e => emit s!"DECLEXT {m} {lvl} {f} {fmtEntries e}"
          | .fdecl f _ _ _ info =>
            if let some dep := info.sorryDep? then
              emit s!"DECLSORRY {m} {lvl} {f} {dep}"
  out.flush

end IRCensusOracle

#eval IRCensusOracle.main

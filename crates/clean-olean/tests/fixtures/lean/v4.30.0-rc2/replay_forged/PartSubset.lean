import Lean
open Lean

/-!
# `PartSubset` — the premise of R113's artifact rule, measured on a toolchain's own output

A `lean --run` CHECKER, not a module source:

    lean --run PartSubset.lean <lib/lean>

reads every `.olean` artifact under `<lib/lean>` with Lean's own `readModuleDataParts` and checks
the rule Clean's one artifact reader (`clean_olean::read_artifact`) enforces:

1. every part states the same `isModule` and import list;
2. for a module-system artifact, every constant of its `.olean` and `.olean.server` is a constant
   of its `.olean.private` (the part a consumer that is not a `module` reads); for any other
   artifact, its companions declare nothing its `.olean` does not;
3. where two parts both hold a name, they hold the same record, or the earlier part holds a
   value-free `axiom` stub of the later part's value (same universe parameters and type).

It also counts how often the two records share their type and value objects (Lean's compactor
writes the parts of one module through one object table), which is what makes Clean's check cheap.
Measured on the repository-pinned v4.30.0-rc2 `lib/lean` (2026-10-22): 2,302 artifacts (2,300
module-system), 314,344 exported/server names, 0 misplaced; 471,516 names held by two parts, 0
disagreements, 166,726 stub completions; every pair shares its type object, and all 188,940
pairs that both carry a value share it. A violation prints its artifact, part(s) and name, and
the script exits 1.
-/

partial def walk (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← walk e.path)
    else if e.path.extension == some "olean" then out := out.push e.path
  return out

def names (d : ModuleData) : NameSet := d.constants.foldl (fun s c => s.insert c.name) {}

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "defn" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def value? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value
  | _ => none

/-- Rule 3 over the records of one name, `a` from an earlier part and `b` from a later one. -/
def agree (a b : ConstantInfo) : Bool :=
  let sameDecl := a.levelParams == b.levelParams && a.type == b.type
  match value? a, value? b with
  | some va, some vb => sameDecl && kindOf a == kindOf b && va == vb
  | none, some _ => sameDecl && kindOf a == "axiom"
  | some _, none => false
  | none, none => sameDecl && kindOf a == kindOf b &&
      (match a, b with
       | .inductInfo x, .inductInfo y => x.numParams == y.numParams && x.numIndices == y.numIndices &&
           x.all == y.all && x.ctors == y.ctors && x.isRec == y.isRec &&
           x.isReflexive == y.isReflexive && x.numNested == y.numNested && x.isUnsafe == y.isUnsafe
       | .ctorInfo x, .ctorInfo y => x.induct == y.induct && x.cidx == y.cidx &&
           x.numParams == y.numParams && x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
       | .recInfo x, .recInfo y => x.all == y.all && x.numParams == y.numParams &&
           x.numIndices == y.numIndices && x.numMotives == y.numMotives &&
           x.numMinors == y.numMinors && x.k == y.k && x.isUnsafe == y.isUnsafe &&
           x.rules.length == y.rules.length &&
           (x.rules.zip y.rules).all (fun (r, s) => r.ctor == s.ctor && r.nfields == s.nfields && r.rhs == s.rhs)
       | _, _ => true)

unsafe def main (args : List String) : IO UInt32 := do
  let [root] := args | IO.eprintln "usage: <lib/lean>"; return 2
  let files ← walk root
  let mut modules := 0
  let mut bad := 0
  let mut placed := 0
  let mut pairs := 0
  let mut stubs := 0
  let mut typeShared := 0
  let mut bothValued := 0
  let mut valueShared := 0
  for f in files do
    let s := OLeanLevel.server.adjustFileName f
    let p := OLeanLevel.private.adjustFileName f
    let hasS ← s.pathExists
    let hasP ← p.pathExists
    let parts := if hasS && hasP then #[f, s, p] else if hasS then #[f, s] else #[f]
    let datas := (← readModuleDataParts parts).map (·.1)
    let some base := datas[0]? | IO.println s!"NO-BASE {f}"; bad := bad + 1; continue
    -- 1. one header
    for d in datas do
      unless d.isModule == base.isModule do IO.println s!"MODULE-FLAG {f}"; bad := bad + 1
      unless d.imports.map (·.module) == base.imports.map (·.module) do
        IO.println s!"IMPORTS {f}"; bad := bad + 1
    -- 2. placement
    if base.isModule then
      modules := modules + 1
      let some priv := datas[2]? | IO.println s!"MODULE-MISSING-PART {f}"; bad := bad + 1; continue
      let privNames := names priv
      for (d, lbl) in (datas.toList.take 2).zip ["olean", "server"] do
        for c in d.constants do
          placed := placed + 1
          unless privNames.contains c.name do
            IO.println s!"NOT-IN-PRIVATE {f} {lbl} {c.name}"; bad := bad + 1
    else
      let b := names base
      for d in datas.toList.drop 1 do
        for c in d.constants do
          unless b.contains c.name do
            IO.println s!"NONMODULE-COMPANION-EXTRA {f} {c.name}"; bad := bad + 1
    -- 3. one record per name
    let tables := datas.map fun d =>
      d.constants.foldl (fun (m : NameMap ConstantInfo) c => m.insert c.name c) {}
    for i in [0:datas.size] do
      for j in [i+1:datas.size] do
        for c in datas[i]!.constants do
          if let some d := tables[j]!.find? c.name then
            pairs := pairs + 1
            if ptrAddrUnsafe c.type == ptrAddrUnsafe d.type then typeShared := typeShared + 1
            if value? c == none && value? d != none then stubs := stubs + 1
            if let (some va, some vb) := (value? c, value? d) then
              bothValued := bothValued + 1
              if ptrAddrUnsafe va == ptrAddrUnsafe vb then valueShared := valueShared + 1
            unless agree c d do
              IO.println s!"DISAGREE {f} parts {i}/{j} {c.name} {kindOf c}/{kindOf d}"; bad := bad + 1
  IO.println s!"checked {files.size} artifacts: {modules} module-system; {placed} exported/server names placed; {pairs} names in two parts ({stubs} stub completions, {typeShared} sharing the type, {valueShared} of {bothValued} valued pairs sharing the value); violations {bad}"
  return if bad == 0 then 0 else 1

import Lean
import Lean.Compiler.IR.EmitUtil
open Lean

def externalEntryJson : ExternEntry → Json
  | .adhoc b => toJson ["adhoc", toString b]
  | .standard b s => toJson ["standard", toString b, s]
  | .inline b s => toJson ["inline", toString b, s]
  | .opaque => toJson ["opaque"]

def nameParts : Name → List Json
  | .anonymous => []
  | .str parent text => nameParts parent ++ [toJson text]
  | .num parent number => nameParts parent ++ [toJson number]

def rowJson (env : Environment) (d : IR.Decl) : Json :=
  let info := d.getInfo
  let ex := match d with
    | .extern (ext := e) .. => toJson (e.entries.map externalEntryJson)
    | _ => Json.null
  Json.mkObj [("text", toJson (toString d)), ("typedName", toJson (nameParts d.name)), ("name", toJson d.name.toString),
    ("extern", ex), ("maxJp", toJson info.maxJp), ("maxVar", toJson info.maxVar),
    ("sorry", toJson (info.sorryDep?.map toString)),
    ("nameForC", toJson (getExternNameFor env `c d.name))]

def observe (env : Environment) (root : Name) : IO Json := do
  let mut nodes := #[root]
  let mut seen : NameSet := {}
  let mut idx := 0
  let mut rows := #[]
  while idx < nodes.size do
    let name := nodes[idx]!
    idx := idx+1
    if seen.contains name then continue
    seen := seen.insert name
    let some d := IR.findEnvDecl env name | throw (IO.userError s!"no runtime definition for {name}")
    let some owner := env.getModuleIdxFor? name | throw (IO.userError s!"no runtime origin for {name}")
    let mod := env.header.modules[owner.toNat]!
    let ir := (IR.declMapExt.getModuleIREntries env owner).find? (·.name == name)
    let base := (IR.declMapExt.getModuleEntries env owner).find? (·.name == name)
    let some selected := ir <|> base | throw (IO.userError s!"no captured runtime row for {name}")
    if rowJson env selected != rowJson env d then throw (IO.userError s!"alternate runtime row for {name}")
    let deps := (IR.collectUsedDecls env [d]).filter (· != name)
    rows := rows.push (Json.mkObj [("owner", toJson mod.module.toString),
       ("phase", toJson (reprStr mod.irPhases)), ("source", toJson (if ir.isSome then "IR" else "main")),
       ("edges", toJson (deps.map toString)), ("record", rowJson env d)])
    nodes := nodes ++ deps
  return Json.mkObj [("root", toJson root.toString), ("rows", toJson rows)]

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Init.System.IO }] {} (loadExts := true)
  IO.println (Json.mkObj [("graph", toJson (env.header.modules.map fun m =>
    Json.mkObj [("name", toJson m.module.toString), ("phase", toJson (reprStr m.irPhases))]))]).compress
  for root in [`Char.toLower, `Nat.repr, `Nat.reprFast, `String.append, `String.Pos.Raw.get,
      `String.Pos.Raw.set, `UInt32.toNat, `UInt32.toUSize, `USize.repr, `String.decapitalize, `IO.Error.toString] do
    let chosen := (Lean.Compiler.getImplementedBy? env root).getD root
    try
      IO.println (Json.mkObj [("declared", toJson root.toString), ("selected", toJson chosen.toString),
        ("result", ← observe env chosen)]).compress
    catch ex =>
      IO.println (Json.mkObj [("declared", toJson root.toString), ("selected", toJson chosen.toString),
        ("failure", toJson (toString ex))]).compress

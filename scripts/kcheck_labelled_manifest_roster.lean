/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import Lean

/-! Untrusted W3 evidence producer. Read pinned Lean's own raw module data;
do not implement a meaning hash or select declarations by namespace. The
current 425-module package and its import-only aggregate fixture uses ordinary (non-`module`-header) artifacts. A
different representation is an explicit prerequisite, never an omission. -/
open Lean

private def nameParts : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameParts p).push (Json.mkObj [("kind", toJson "str"), ("value", toJson s)])
  | .num p n => (nameParts p).push (Json.mkObj [("kind", toJson "num"), ("value", toJson n)])

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def safety : ConstantInfo → String
  | .defnInfo v => match v.safety with
    | .safe => "safe"
    | .unsafe => "unsafe"
    | .partial => "partial"
  | .axiomInfo v => if v.isUnsafe then "unsafe" else "safe"
  | .opaqueInfo v => if v.isUnsafe then "unsafe" else "safe"
  | .inductInfo v => if v.isUnsafe then "unsafe" else "safe"
  | .ctorInfo v => if v.isUnsafe then "unsafe" else "safe"
  | .recInfo v => if v.isUnsafe then "unsafe" else "safe"
  | _ => "safe"

def main (paths : List String) : IO UInt32 := do
  try
    if paths.isEmpty then throw <| IO.userError "W3_ROSTER_EMPTY_INPUT"
    let mut regions : Array CompactedRegion := #[]
    let mut modules : Array Json := #[]
    for path in paths do
      let loaded ← readModuleDataParts #[System.FilePath.mk path]
      unless loaded.size == 1 do throw <| IO.userError s!"W3_ROSTER_PART_COUNT {path}"
      let some (md, region) := loaded[0]?
        | throw <| IO.userError s!"W3_ROSTER_MISSING_PART {path}"
      regions := regions.push region
      if md.isModule then throw <| IO.userError s!"W3_ROSTER_MODULE_HEADER_PREREQUISITE {path}"
      unless md.constNames == md.constants.map (·.name) do
        throw <| IO.userError s!"W3_ROSTER_NAMES_RECORDS_DISAGREE {path}"
      let rows := md.constants.map fun ci => Json.mkObj [
        ("name", Json.arr (nameParts ci.name)), ("kind", toJson (kind ci)),
        ("safety", toJson (safety ci))]
      modules := modules.push <| Json.mkObj [
        ("path", toJson path), ("declarations", Json.arr rows),
        ("extra_names", Json.arr (md.extraConstNames.map fun n => Json.arr (nameParts n)))]
    IO.println <| (Json.mkObj [("schema", toJson (1 : Nat)),
      ("modules", Json.arr modules), ("regions_kept", toJson regions.size)]).compress
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"W3_ROSTER_REFUSED {e}"
    return (1 : UInt32)
